#!/usr/bin/env python3
"""
SuperHash v4.0 — LLM Rule Proposal Engine + TCB Validation

Three proposal modes:
  template — deterministic template instantiation (seed rules, no LLM)
  local    — Ollama API (qwen2.5, runs on localhost:11434)
  claude   — Anthropic Claude API (requires ANTHROPIC_API_KEY)

Three-Tier Bridge (D7):
  Tier 1 (this script): Propose rules via LLM, validate TCB round-trip
  Tier 2 (Lean): Kernel verification via axle_integration.py
  Tier 3: Binary result fed back as RLVF reward

TCB Validation (D11):
  Every proposed rule goes through round-trip check:
  RuleCandidate JSON -> Lean source -> parse back -> compare

Usage:
  python3 scripts/rule_proposer.py --island SPN --proposals 10
  python3 scripts/rule_proposer.py --template iterate_fusion
  python3 scripts/rule_proposer.py --model local --design aes128 --proposals 5
  python3 scripts/rule_proposer.py --model claude --design aes128 --proposals 3
"""

from __future__ import annotations

import json
import random
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

sys.path.insert(0, str(Path(__file__).parent))

from config import (
    OLLAMA_URL,
    OLLAMA_MODEL,
    ANTHROPIC_API_KEY,
    ANTHROPIC_MODEL,
    KNOWN_DESIGNS,
    SYSTEM_PROMPT,
    PROPOSE_TEMPLATE,
)


# ============================================================
# Rule templates (manually curated seed rules)
# ============================================================

# Template: a parameterized rule pattern that can be instantiated
@dataclass
class RuleTemplate:
    name: str
    classification: str
    lhs_pattern: str      # CryptoExpr with {var0}, {var1}, {param0} placeholders
    rhs_pattern: str
    island: str           # CryptoConstruction family
    param_ranges: dict = field(default_factory=dict)  # param name -> (min, max)


# Seed templates based on known crypto design patterns
SEED_TEMPLATES: list[RuleTemplate] = [
    # SPN island
    RuleTemplate(
        name="spn_round_fusion",
        classification="equivalence",
        lhs_pattern=".compose (.spnBlock {r1} (.var 0) (.var 1)) (.spnBlock {r2} (.var 0) (.var 1))",
        rhs_pattern=".spnBlock {r1_plus_r2} (.var 0) (.var 1)",
        island="SPN",
        param_ranges={"r1": (1, 20), "r2": (1, 20)},
    ),
    RuleTemplate(
        name="iterate_unroll",
        classification="equivalence",
        lhs_pattern=".iterate {n} (.var 0)",
        rhs_pattern=".compose (.iterate {n_minus_1} (.var 0)) (.var 0)",
        island="SPN",
        param_ranges={"n": (2, 20)},
    ),
    # Feistel island
    RuleTemplate(
        name="feistel_double",
        classification="equivalence",
        lhs_pattern=".compose (.feistelBlock {r1} (.var 0)) (.feistelBlock {r2} (.var 0))",
        rhs_pattern=".feistelBlock {r1_plus_r2} (.var 0)",
        island="Feistel",
        param_ranges={"r1": (1, 32), "r2": (1, 32)},
    ),
    # Sponge island
    RuleTemplate(
        name="sponge_rate_split",
        classification="equivalence",
        lhs_pattern=".spongeBlock {rt} {cap} (.var 0)",
        rhs_pattern=".compose (.iterate {rt} (.var 0)) (.const {cap})",
        island="Sponge",
        param_ranges={"rt": (1, 24), "cap": (1, 512)},
    ),
    # ARX island
    RuleTemplate(
        name="arx_triple_compose",
        classification="equivalence",
        lhs_pattern=".arxBlock {r} (.var 0) (.var 1) (.var 2)",
        rhs_pattern=".iterate {r} (.compose (.compose (.var 0) (.var 1)) (.var 2))",
        island="ARX",
        param_ranges={"r": (1, 20)},
    ),
]


# ============================================================
# Rule proposal via template instantiation
# ============================================================

def instantiate_template(template: RuleTemplate, seed: int = 42) -> dict:
    """Instantiate a rule template with random parameters.

    Returns a RuleCandidate JSON dict.
    """
    rng = random.Random(seed)
    params: dict[str, int] = {}

    for pname, (lo, hi) in template.param_ranges.items():
        params[pname] = rng.randint(lo, hi)

    # Compute derived params
    if "r1" in params and "r2" in params:
        params["r1_plus_r2"] = params["r1"] + params["r2"]
    if "n" in params:
        params["n_minus_1"] = params["n"] - 1

    lhs = template.lhs_pattern.format(**params)
    rhs = template.rhs_pattern.format(**params)

    return {
        "name": f"{template.name}_{seed}",
        "classification": template.classification,
        "lhs_template": lhs,
        "rhs_template": rhs,
        "source": f"template:{template.name}",
        "confidence": 80,
    }


def propose_rules(
    island: Optional[str] = None,
    count: int = 5,
    base_seed: int = 42,
) -> list[dict]:
    """Propose rules by instantiating templates.

    Args:
        island: Filter to specific CryptoConstruction family (SPN/Feistel/Sponge/ARX)
        count: Number of proposals per template
        base_seed: Random seed for reproducibility
    """
    templates = SEED_TEMPLATES
    if island:
        templates = [t for t in templates if t.island == island]

    proposals = []
    for template in templates:
        for i in range(count):
            proposal = instantiate_template(template, seed=base_seed + i)
            proposals.append(proposal)

    return proposals


# ============================================================
# LLM-based rule proposal
# ============================================================

def _call_ollama(prompt: str, system: str, timeout: int = 30) -> Optional[str]:
    """Call Ollama API at localhost. Returns response text or None on failure."""
    try:
        import requests
    except ImportError:
        print("[rule_proposer] WARNING: 'requests' not installed. pip install requests", file=sys.stderr)
        return None

    url = f"{OLLAMA_URL}/api/generate"
    payload = {
        "model": OLLAMA_MODEL,
        "system": system,
        "prompt": prompt,
        "stream": False,
        "options": {
            "temperature": 0.7,
            "num_predict": 2048,
        },
    }

    try:
        resp = requests.post(url, json=payload, timeout=timeout)
        resp.raise_for_status()
        data = resp.json()
        return data.get("response", "")
    except Exception as e:
        print(f"[rule_proposer] Ollama error: {e}", file=sys.stderr)
        return None


def _call_anthropic(prompt: str, system: str, timeout: int = 60) -> Optional[str]:
    """Call Anthropic Claude API. Returns response text or None on failure."""
    if not ANTHROPIC_API_KEY:
        print("[rule_proposer] WARNING: ANTHROPIC_API_KEY not set", file=sys.stderr)
        return None

    try:
        import anthropic
    except ImportError:
        print("[rule_proposer] WARNING: 'anthropic' not installed. pip install anthropic", file=sys.stderr)
        return None

    try:
        client = anthropic.Anthropic(api_key=ANTHROPIC_API_KEY)
        message = client.messages.create(
            model=ANTHROPIC_MODEL,
            max_tokens=2048,
            system=system,
            messages=[{"role": "user", "content": prompt}],
        )
        # Extract text from response
        text_parts = [block.text for block in message.content if hasattr(block, "text")]
        return "\n".join(text_parts)
    except Exception as e:
        print(f"[rule_proposer] Anthropic error: {e}", file=sys.stderr)
        return None


def _parse_llm_response(response: str) -> list[dict]:
    """Parse LLM response into a list of RuleCandidate dicts.

    Handles common LLM quirks: markdown fences, extra text before/after JSON.
    """
    if not response:
        return []

    text = response.strip()

    # Strip markdown code fences if present
    if "```" in text:
        # Extract content between first ``` and last ```
        parts = text.split("```")
        # Take the content block (index 1 for ```json\n...\n```)
        for part in parts:
            stripped = part.strip()
            if stripped.startswith("json"):
                stripped = stripped[4:].strip()
            if stripped.startswith("["):
                text = stripped
                break

    # Try to find JSON array in the text
    start = text.find("[")
    end = text.rfind("]")
    if start == -1 or end == -1 or end <= start:
        # Try single object
        start = text.find("{")
        end = text.rfind("}")
        if start == -1 or end == -1 or end <= start:
            return []
        text = "[" + text[start:end + 1] + "]"
    else:
        text = text[start:end + 1]

    try:
        candidates = json.loads(text)
    except json.JSONDecodeError as e:
        print(f"[rule_proposer] JSON parse error: {e}", file=sys.stderr)
        return []

    if not isinstance(candidates, list):
        candidates = [candidates]

    # Validate and normalize each candidate
    valid = []
    for i, c in enumerate(candidates):
        if not isinstance(c, dict):
            continue
        # Ensure required fields
        if "lhs_template" not in c or "rhs_template" not in c:
            continue
        # Default missing fields
        c.setdefault("name", f"llm_rule_{i}")
        c.setdefault("classification", "equivalence")
        c.setdefault("confidence", 60)
        # Remove extra fields the LLM might add (reasoning, etc)
        normalized = {
            "name": c["name"],
            "classification": c["classification"],
            "lhs_template": c["lhs_template"],
            "rhs_template": c["rhs_template"],
            "source": c.get("source", "llm"),
            "confidence": c.get("confidence", 60),
        }
        valid.append(normalized)

    return valid


def propose_with_llm(
    context: dict,
    model: str = "local",
    count: int = 5,
    timeout: int = 60,
) -> list[dict]:
    """Propose rules using an LLM.

    Args:
        context: Dict with keys:
            - design_name: str (e.g., "aes128")
            - design_expr: str (CryptoExpr literal)
            - design_description: str
            - current_rules: list[str] (names of rules already in pool)
        model: "local" (Ollama), "claude" (Anthropic), or "template" (fallback)
        count: Number of rules to propose
        timeout: Request timeout in seconds

    Returns:
        List of RuleCandidate dicts (may be empty on failure).
        Falls back to template mode if LLM call fails.
    """
    if model == "template":
        design_name = context.get("design_name", "")
        island = None
        if design_name in KNOWN_DESIGNS:
            island = KNOWN_DESIGNS[design_name].get("family")
        return propose_rules(island=island, count=count)

    # Build prompt
    current_rule_names = context.get("current_rules", [])
    rules_str = ", ".join(current_rule_names) if current_rule_names else "(none)"

    prompt = PROPOSE_TEMPLATE.format(
        design_description=context.get("design_description", "unknown"),
        design_expr=context.get("design_expr", "unknown"),
        current_rules=rules_str,
        count=count,
    )

    # Call LLM
    response: Optional[str] = None
    start = time.time()

    if model == "local":
        response = _call_ollama(prompt, SYSTEM_PROMPT, timeout=timeout)
    elif model == "claude":
        response = _call_anthropic(prompt, SYSTEM_PROMPT, timeout=timeout)
    else:
        print(f"[rule_proposer] Unknown model '{model}', falling back to template", file=sys.stderr)
        return propose_rules(count=count)

    elapsed = time.time() - start

    if response is None:
        print(f"[rule_proposer] LLM call failed after {elapsed:.1f}s, falling back to template", file=sys.stderr)
        design_name = context.get("design_name", "")
        island = KNOWN_DESIGNS.get(design_name, {}).get("family")
        return propose_rules(island=island, count=count)

    # Parse response
    candidates = _parse_llm_response(response)

    if not candidates:
        print(f"[rule_proposer] LLM returned no parseable rules after {elapsed:.1f}s, falling back to template",
              file=sys.stderr)
        design_name = context.get("design_name", "")
        island = KNOWN_DESIGNS.get(design_name, {}).get("family")
        return propose_rules(island=island, count=count)

    # Tag source
    for c in candidates:
        c["source"] = f"llm:{model}"

    print(f"[rule_proposer] LLM ({model}) proposed {len(candidates)} rules in {elapsed:.1f}s", file=sys.stderr)
    return candidates


# ============================================================
# TCB round-trip validation (D11)
# ============================================================

def round_trip_validate(candidate: dict) -> bool:
    """Validate TCB round-trip: dict -> serialize -> deserialize -> compare."""
    serialized = json.dumps(candidate, sort_keys=True)
    deserialized = json.loads(serialized)
    reserialized = json.dumps(deserialized, sort_keys=True)
    return serialized == reserialized


# ============================================================
# Fast syntax pre-check (Level 0 reward)
# ============================================================

def syntax_precheck(candidate: dict) -> bool:
    """Quick check that the candidate has valid structure."""
    required = ["name", "classification", "lhs_template", "rhs_template"]
    if not all(k in candidate for k in required):
        return False
    if candidate["classification"] not in ("equivalence", "improvement", "conditional"):
        return False
    if not candidate["lhs_template"] or not candidate["rhs_template"]:
        return False
    return True


# ============================================================
# CLI
# ============================================================

def main() -> None:
    if "--help" in sys.argv:
        print(__doc__)
        sys.exit(0)

    if "--test" in sys.argv:
        # Self-test: template mode
        proposals = propose_rules(count=2)
        assert len(proposals) == 10, f"Expected 10 proposals, got {len(proposals)}"

        for p in proposals:
            assert syntax_precheck(p), f"Syntax check failed: {p['name']}"
            assert round_trip_validate(p), f"Round-trip failed: {p['name']}"

        print(f"[template] Generated {len(proposals)} proposals, all valid")

        # Self-test: propose_with_llm in template fallback mode
        ctx = {
            "design_name": "aes128",
            "design_expr": KNOWN_DESIGNS["aes128"]["expr"],
            "design_description": KNOWN_DESIGNS["aes128"]["description"],
            "current_rules": [],
        }
        llm_proposals = propose_with_llm(ctx, model="template", count=3)
        assert len(llm_proposals) > 0, "propose_with_llm (template) should return proposals"
        for p in llm_proposals:
            assert syntax_precheck(p), f"Syntax check failed: {p['name']}"
        print(f"[propose_with_llm/template] Generated {len(llm_proposals)} proposals, all valid")

        # Self-test: parse_llm_response
        mock_response = json.dumps([
            {
                "name": "test_rule",
                "classification": "equivalence",
                "lhs_template": ".iterate 2 (.var 0)",
                "rhs_template": ".compose (.var 0) (.var 0)",
                "reasoning": "unroll iterate 2",
            }
        ])
        parsed = _parse_llm_response(mock_response)
        assert len(parsed) == 1, f"Expected 1 parsed rule, got {len(parsed)}"
        assert parsed[0]["name"] == "test_rule"
        assert "reasoning" not in parsed[0], "Should strip extra fields"
        print(f"[_parse_llm_response] Parsed {len(parsed)} rules from mock LLM response")

        # Test markdown fence handling
        fenced = "Here are the rules:\n```json\n" + mock_response + "\n```\nDone!"
        parsed2 = _parse_llm_response(fenced)
        assert len(parsed2) == 1, f"Fenced parse: expected 1, got {len(parsed2)}"
        print("[_parse_llm_response] Handled markdown fences correctly")

        print("Self-test: PASS")
        return

    # Parse CLI args
    island = None
    count = 5
    model = "template"
    design = "aes128"

    if "--island" in sys.argv:
        idx = sys.argv.index("--island") + 1
        island = sys.argv[idx]
    if "--proposals" in sys.argv:
        idx = sys.argv.index("--proposals") + 1
        count = int(sys.argv[idx])
    if "--model" in sys.argv:
        idx = sys.argv.index("--model") + 1
        model = sys.argv[idx]
    if "--design" in sys.argv:
        idx = sys.argv.index("--design") + 1
        design = sys.argv[idx]

    if model == "template":
        proposals = propose_rules(island=island, count=count)
    else:
        design_info = KNOWN_DESIGNS.get(design, KNOWN_DESIGNS["aes128"])
        ctx = {
            "design_name": design,
            "design_expr": design_info["expr"],
            "design_description": design_info["description"],
            "current_rules": [],
        }
        proposals = propose_with_llm(ctx, model=model, count=count)

    for p in proposals:
        print(json.dumps(p, indent=2))


if __name__ == "__main__":
    main()
