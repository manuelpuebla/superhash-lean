#!/usr/bin/env python3
"""
SuperHash v4.0 — Configuration for LLM-integrated design loop.

Centralizes settings for LLM endpoints, Lean project paths,
verification timeouts, and loop parameters.

Environment variables:
  ANTHROPIC_API_KEY  — API key for Claude (required for model="claude")
  OLLAMA_URL         — Override Ollama endpoint (default: http://localhost:11434)
  SUPERHASH_MODEL    — Override default model (local/claude/template)
"""

from __future__ import annotations

import os
from pathlib import Path

# ============================================================
# LLM endpoints
# ============================================================

OLLAMA_URL: str = os.environ.get("OLLAMA_URL", "http://localhost:11434")
OLLAMA_MODEL: str = "qwen2.5"

ANTHROPIC_API_KEY: str = os.environ.get("ANTHROPIC_API_KEY", "")
ANTHROPIC_MODEL: str = "claude-sonnet-4-20250514"

DEFAULT_MODEL: str = os.environ.get("SUPERHASH_MODEL", "template")

# ============================================================
# Project paths
# ============================================================

LEAN_PROJECT_DIR: Path = Path(__file__).resolve().parent.parent
SCRIPTS_DIR: Path = Path(__file__).resolve().parent
GEN_DIR: Path = LEAN_PROJECT_DIR / "SuperHash" / "Discovery" / "_gen"

# ============================================================
# Verification
# ============================================================

VERIFICATION_TIMEOUT: int = 60  # seconds per rule verification
MAX_HEARTBEATS: int = 400000    # Lean heartbeat limit for generated proofs

# ============================================================
# Design loop
# ============================================================

MAX_RULES_PER_ROUND: int = 5
MAX_ROUNDS: int = 20
CONVERGENCE_WINDOW: int = 3     # stop if no Pareto improvement for N rounds
MAX_RULES_PER_ISLAND: int = 50

# ============================================================
# Known designs (maps CLI name -> CryptoExpr Lean literal)
# ============================================================

KNOWN_DESIGNS: dict[str, dict] = {
    "aes128": {
        "expr": ".spnBlock 10 (.const 7) (.const 5)",
        "description": "AES-128: 10-round SPN, sbox degree 7, linear branch 5",
        "family": "SPN",
    },
    "poseidon128": {
        "expr": ".spnBlock 8 (.const 5) (.const 4)",
        "description": "Poseidon-128: 8-round SPN, sbox degree 5, linear branch 4",
        "family": "SPN",
    },
    "sha256": {
        "expr": ".feistelBlock 64 (.const 3)",
        "description": "SHA-256-like: 64-round Feistel, round function cost 3",
        "family": "Feistel",
    },
    "keccak": {
        "expr": ".spongeBlock 24 256 (.const 5)",
        "description": "Keccak-like: 24-round sponge, 256 capacity, perm cost 5",
        "family": "Sponge",
    },
    "chacha": {
        "expr": ".arxBlock 20 (.const 1) (.const 1) (.const 1)",
        "description": "ChaCha-like: 20-round ARX, all costs 1",
        "family": "ARX",
    },
}

# ============================================================
# LLM prompts (shared across propose_with_llm)
# ============================================================

SYSTEM_PROMPT: str = """\
You are a cryptographic design assistant specializing in hash function optimization.
You work within the SuperHash formal verification framework (Lean 4).

Your task: propose rewrite rules for cryptographic expressions (CryptoExpr).
A rewrite rule transforms a CryptoExpr LHS into an equivalent RHS, preserving
semantics under all evaluation environments.

CryptoExpr constructors:
  .sbox d child          -- S-box with degree d
  .linear b child        -- linear layer with branch number b
  .xor left right        -- XOR combination
  .round d b child       -- round function (degree d, branch b)
  .compose f g           -- sequential composition f(g(x))
  .parallel left right   -- parallel execution
  .iterate n body        -- repeat body n times
  .const v               -- constant value v
  .var id                -- variable with ID id
  .spnBlock r sbox lin   -- SPN block: r rounds of sbox+linear
  .feistelBlock r func   -- Feistel network: r rounds with func
  .spongeBlock rt cap p  -- sponge: rt rate rounds, cap capacity, perm p
  .arxBlock r add rot xor -- ARX: r rounds of add+rotate+xor

Evaluation semantics (eval env):
  .sbox d c        => d * (c.eval env)
  .linear b c      => b + (c.eval env)
  .xor l r         => (l.eval env) + (r.eval env)
  .round d b c     => d * (c.eval env) + b
  .compose f g     => f.eval env + g.eval env
  .parallel l r    => (l.eval env) + (r.eval env)
  .iterate n b     => n * (b.eval env)
  .const v         => v
  .var id          => env id
  .spnBlock r s l  => r * (s.eval env + l.eval env)
  .feistelBlock r f => r * (f.eval env)
  .spongeBlock rt cap p => rt * (p.eval env) + cap
  .arxBlock r a ro x => r * (a.eval env + ro.eval env + x.eval env)

Rules MUST preserve evaluation semantics: for all env, lhs.eval env = rhs.eval env.
"""

PROPOSE_TEMPLATE: str = """\
Current design: {design_description}
Current CryptoExpr: {design_expr}
Current rules in pool: {current_rules}
Optimization goal: find equivalent expressions with better security/latency/gate tradeoffs.

Propose {count} new rewrite rules. For each rule, output a JSON object:
{{
  "name": "<unique_snake_case_name>",
  "classification": "equivalence",
  "lhs_template": "<CryptoExpr string>",
  "rhs_template": "<CryptoExpr string>",
  "reasoning": "<1-2 sentences explaining why LHS = RHS>"
}}

Output ONLY a JSON array of rule objects, no other text.
"""
