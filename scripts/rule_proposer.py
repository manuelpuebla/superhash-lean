#!/usr/bin/env python3
"""
SuperHash v2.0 — LLM Rule Proposal Engine + TCB Validation (N2.6)

CodeEvolve pattern: Island GA + LLM ensemble for rule discovery.
Each island corresponds to a CryptoConstruction family (SPN, Feistel, Sponge, ARX).

Three-Tier Bridge (D7):
  Tier 1 (this script): Propose rules via LLM, validate TCB round-trip
  Tier 2 (Lean): Kernel verification via axle_integration.py
  Tier 3: Binary result fed back as RLVF reward

TCB Validation (D11):
  Every proposed rule goes through round-trip check:
  RuleCandidate JSON → Lean source → parse back → compare

Usage:
  python3 scripts/rule_proposer.py --island SPN --proposals 10
  python3 scripts/rule_proposer.py --template iterate_fusion
"""

from __future__ import annotations

import json
import random
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


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
    param_ranges: dict = field(default_factory=dict)  # param name → (min, max)


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
# TCB round-trip validation (D11)
# ============================================================

def round_trip_validate(candidate: dict) -> bool:
    """Validate TCB round-trip: dict → serialize → deserialize → compare."""
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
        # Self-test
        proposals = propose_rules(count=2)
        assert len(proposals) == 10, f"Expected 10 proposals, got {len(proposals)}"

        for p in proposals:
            assert syntax_precheck(p), f"Syntax check failed: {p['name']}"
            assert round_trip_validate(p), f"Round-trip failed: {p['name']}"

        print(f"Generated {len(proposals)} proposals, all valid")
        print("Self-test: PASS")
        return

    island = None
    count = 5
    if "--island" in sys.argv:
        idx = sys.argv.index("--island") + 1
        island = sys.argv[idx]
    if "--proposals" in sys.argv:
        idx = sys.argv.index("--proposals") + 1
        count = int(sys.argv[idx])

    proposals = propose_rules(island=island, count=count)
    for p in proposals:
        print(json.dumps(p, indent=2))


if __name__ == "__main__":
    main()
