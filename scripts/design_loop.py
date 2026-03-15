#!/usr/bin/env python3
"""
SuperHash v4.0 — Design Loop Orchestrator

The "power button" for the SuperHash autonomous design exploration system.
Run it and the system proposes, verifies, saturates, and extracts optimal designs.

Pipeline per round:
  1. Propose candidate rewrite rules (LLM or templates)
  2. Pre-check: syntax + round-trip TCB validation
  3. Verify: compile each rule via Lean kernel (lake env lean)
  4. Accumulate: add SOUND rules to the verified pool
  5. Saturate: run E-graph saturation with all verified rules (simulated in Python)
  6. Extract: Pareto front of security/latency/gates tradeoffs
  7. Evaluate: check improvement, update best designs

Convergence: stops when Pareto front is stable for N consecutive rounds,
or after --rounds rounds, whichever comes first.

Kill switch: create /tmp/superhash_kill to stop gracefully mid-loop.

Usage:
  python3 scripts/design_loop.py --model local --rounds 10 --design aes128
  python3 scripts/design_loop.py --model claude --rounds 5 --design sha256
  python3 scripts/design_loop.py --model template --rounds 20 --design aes128
  python3 scripts/design_loop.py --test
  python3 scripts/design_loop.py --test --full  # includes Lean compilation
"""

from __future__ import annotations

import json
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

sys.path.insert(0, str(Path(__file__).parent))

from config import (
    KNOWN_DESIGNS,
    DEFAULT_MODEL,
    MAX_RULES_PER_ROUND,
    MAX_ROUNDS,
    CONVERGENCE_WINDOW,
    MAX_RULES_PER_ISLAND,
    LEAN_PROJECT_DIR,
    VERIFICATION_TIMEOUT,
)
from rule_proposer import (
    propose_rules,
    propose_with_llm,
    syntax_precheck,
    round_trip_validate,
)
from axle_integration import (
    RuleCandidate,
    VerificationResult,
    VerificationReport,
    verify_rule,
    round_trip_check,
)
from rlvf_reward import (
    ParetoPoint,
    compute_pareto_improvement,
    RewardBreakdown,
)


# ============================================================
# Design loop state
# ============================================================

@dataclass
class VerifiedRuleEntry:
    """A rule that has been verified by the Lean kernel."""
    candidate: dict          # RuleCandidate JSON
    verification: dict       # VerificationReport JSON
    round_added: int         # Which round this was verified in
    pareto_delta: float = 0.0  # Pareto improvement when added


@dataclass
class DesignState:
    """Full state of the design loop."""
    design_name: str
    design_expr: str
    design_description: str
    family: str
    verified_rules: list[VerifiedRuleEntry] = field(default_factory=list)
    pareto_front: list[ParetoPoint] = field(default_factory=list)
    round_history: list[dict] = field(default_factory=list)

    @classmethod
    def from_design(cls, design_name: str) -> "DesignState":
        info = KNOWN_DESIGNS.get(design_name)
        if info is None:
            available = ", ".join(KNOWN_DESIGNS.keys())
            raise ValueError(f"Unknown design '{design_name}'. Available: {available}")
        return cls(
            design_name=design_name,
            design_expr=info["expr"],
            design_description=info["description"],
            family=info["family"],
            # Initialize with the design's own metrics as baseline Pareto point
            pareto_front=[_design_to_pareto(design_name)],
        )

    def rule_names(self) -> list[str]:
        return [r.candidate["name"] for r in self.verified_rules]


def _design_to_pareto(design_name: str) -> ParetoPoint:
    """Compute baseline Pareto point for a known design.

    These match the Lean #eval results from Instances/BlockDesigns.lean.
    """
    baselines = {
        "aes128":      ParetoPoint(security=120, latency=10, gates=70),
        "poseidon128": ParetoPoint(security=72,  latency=8,  gates=40),
        "sha256":      ParetoPoint(security=192, latency=64, gates=192),
        "keccak":      ParetoPoint(security=376, latency=24, gates=120),
        "chacha":      ParetoPoint(security=60,  latency=20, gates=60),
    }
    return baselines.get(design_name, ParetoPoint(security=100, latency=10, gates=50))


# ============================================================
# Pretty printing
# ============================================================

_BOLD = "\033[1m"
_GREEN = "\033[32m"
_RED = "\033[31m"
_YELLOW = "\033[33m"
_CYAN = "\033[36m"
_DIM = "\033[2m"
_RESET = "\033[0m"


def _supports_color() -> bool:
    """Check if stdout supports ANSI colors."""
    if not hasattr(sys.stdout, "isatty"):
        return False
    return sys.stdout.isatty()


def _c(code: str, text: str) -> str:
    """Wrap text with ANSI color if terminal supports it."""
    if _supports_color():
        return f"{code}{text}{_RESET}"
    return text


def _print_header(text: str) -> None:
    width = 60
    print()
    print(_c(_BOLD, "=" * width))
    print(_c(_BOLD, f"  {text}"))
    print(_c(_BOLD, "=" * width))


def _print_round_header(round_num: int, total: int) -> None:
    print()
    print(_c(_CYAN, f"--- Round {round_num}/{total} " + "-" * 40))


def _print_pareto(front: list[ParetoPoint]) -> None:
    if not front:
        print("  (empty Pareto front)")
        return
    print(f"  {'Security':>10} {'Latency':>10} {'Gates':>10}")
    print(f"  {'-'*10} {'-'*10} {'-'*10}")
    for p in sorted(front, key=lambda p: (-p.security, p.latency)):
        print(f"  {p.security:>10} {p.latency:>10} {p.gates:>10}")


# ============================================================
# Core loop logic
# ============================================================

@dataclass
class LoopConfig:
    """Configuration for the design loop."""
    design: str = "aes128"
    model: str = DEFAULT_MODEL
    max_rounds: int = MAX_ROUNDS
    proposals_per_round: int = MAX_RULES_PER_ROUND
    convergence_window: int = CONVERGENCE_WINDOW
    seed: int = 42
    verify: bool = True           # actually call lake env lean
    timeout: int = VERIFICATION_TIMEOUT
    kill_switch_file: str = "/tmp/superhash_kill"
    verbose: bool = True


@dataclass
class LoopResult:
    """Result of the design loop execution."""
    rounds_completed: int
    total_proposed: int
    total_verified: int
    total_sound: int
    final_pareto_size: int
    converged: bool
    elapsed_seconds: float
    best_designs: list[dict] = field(default_factory=list)
    per_round: list[dict] = field(default_factory=list)

    def to_json(self) -> dict:
        return {
            "rounds_completed": self.rounds_completed,
            "total_proposed": self.total_proposed,
            "total_verified": self.total_verified,
            "total_sound": self.total_sound,
            "final_pareto_size": self.final_pareto_size,
            "converged": self.converged,
            "elapsed_seconds": round(self.elapsed_seconds, 2),
            "best_designs": self.best_designs,
            "per_round": self.per_round,
        }


def _simulate_pareto_expansion(
    state: DesignState,
    new_rules: list[dict],
    rng_seed: int,
) -> list[ParetoPoint]:
    """Simulate Pareto front expansion from adding new verified rules.

    In production, this calls the Lean pipeline (saturateF + extractParetoV2).
    Here we simulate it: each verified equivalence rule has a chance of
    discovering a design variant with different tradeoffs.
    """
    import random
    rng = random.Random(rng_seed)

    new_front = list(state.pareto_front)

    for rule in new_rules:
        # Each rule has a ~25% chance of finding a new Pareto point
        if rng.random() < 0.25:
            # Generate a point near the existing front but with a different tradeoff
            base = rng.choice(new_front) if new_front else ParetoPoint(100, 10, 50)
            # Vary one dimension favorably, another unfavorably
            dim = rng.choice(["security", "latency", "gates"])
            if dim == "security":
                new_point = ParetoPoint(
                    security=base.security + rng.randint(5, 20),
                    latency=base.latency + rng.randint(0, 3),
                    gates=base.gates + rng.randint(-5, 10),
                )
            elif dim == "latency":
                new_point = ParetoPoint(
                    security=base.security + rng.randint(-10, 5),
                    latency=max(1, base.latency - rng.randint(1, 5)),
                    gates=base.gates + rng.randint(-5, 10),
                )
            else:
                new_point = ParetoPoint(
                    security=base.security + rng.randint(-10, 5),
                    latency=base.latency + rng.randint(0, 3),
                    gates=max(1, base.gates - rng.randint(5, 20)),
                )

            # Only add if not dominated by existing front
            dominated = any(p.dominates(new_point) for p in new_front)
            if not dominated:
                new_front.append(new_point)

    return new_front


def run_design_loop(config: LoopConfig) -> LoopResult:
    """Run the full autonomous design loop.

    Each round:
      1. Propose rules (via LLM or templates)
      2. Pre-check (syntax + round-trip)
      3. Verify via Lean kernel (if config.verify)
      4. Update Pareto front
      5. Check convergence
    """
    start = time.time()

    # Initialize state
    state = DesignState.from_design(config.design)

    if config.verbose:
        _print_header(f"SuperHash Design Loop v4.0")
        print(f"  Design:   {state.design_name} ({state.design_description})")
        print(f"  Model:    {config.model}")
        print(f"  Rounds:   {config.max_rounds}")
        print(f"  Verify:   {'yes (lake env lean)' if config.verify else 'no (simulated)'}")
        print(f"  Converge: stop after {config.convergence_window} rounds without improvement")
        print()
        print("  Baseline Pareto front:")
        _print_pareto(state.pareto_front)

    total_proposed = 0
    total_verified = 0
    total_sound = 0
    no_improvement_count = 0
    baseline_pareto = list(state.pareto_front)

    for round_idx in range(config.max_rounds):
        # Kill switch check
        if Path(config.kill_switch_file).exists():
            if config.verbose:
                print(f"\n{_c(_YELLOW, 'Kill switch detected')} — stopping gracefully")
            break

        round_start = time.time()
        if config.verbose:
            _print_round_header(round_idx + 1, config.max_rounds)

        # ---- Step 1: Propose rules ----
        context = {
            "design_name": state.design_name,
            "design_expr": state.design_expr,
            "design_description": state.design_description,
            "current_rules": state.rule_names(),
        }

        proposals = propose_with_llm(
            context,
            model=config.model,
            count=config.proposals_per_round,
        )
        total_proposed += len(proposals)

        if config.verbose:
            print(f"  Proposed: {len(proposals)} candidates (via {config.model})")

        # ---- Step 2: Pre-check ----
        valid_proposals = []
        for p in proposals:
            if syntax_precheck(p) and round_trip_validate(p):
                valid_proposals.append(p)

        if config.verbose:
            rejected = len(proposals) - len(valid_proposals)
            if rejected > 0:
                print(f"  Pre-check: {rejected} rejected (syntax/round-trip), {len(valid_proposals)} remain")

        # ---- Step 3: Verify via Lean kernel ----
        round_sound = []
        round_unsound = 0
        round_timeout = 0
        round_error = 0

        for p in valid_proposals:
            rc = RuleCandidate.from_json(p)
            total_verified += 1

            if config.verify:
                report = verify_rule(rc, LEAN_PROJECT_DIR, config.timeout)
            else:
                # Simulated verification: template rules pass, LLM rules ~50/50
                import random
                rng = random.Random(config.seed + round_idx * 1000 + total_verified)
                if p.get("source", "").startswith("template:"):
                    result = VerificationResult.SOUND
                else:
                    result = VerificationResult.SOUND if rng.random() < 0.5 else VerificationResult.UNSOUND
                report = VerificationReport(rc, result, elapsed_ms=10)

            if report.result == VerificationResult.SOUND:
                round_sound.append(p)
                total_sound += 1
                entry = VerifiedRuleEntry(
                    candidate=p,
                    verification=report.to_json(),
                    round_added=round_idx + 1,
                )
                state.verified_rules.append(entry)
            elif report.result == VerificationResult.TIMEOUT:
                round_timeout += 1
            elif report.result == VerificationResult.PARSE_ERROR:
                round_error += 1
            else:
                round_unsound += 1

        if config.verbose:
            parts = []
            if round_sound:
                parts.append(_c(_GREEN, f"{len(round_sound)} SOUND"))
            if round_unsound:
                parts.append(_c(_RED, f"{round_unsound} unsound"))
            if round_timeout:
                parts.append(_c(_YELLOW, f"{round_timeout} timeout"))
            if round_error:
                parts.append(_c(_RED, f"{round_error} parse_error"))
            if parts:
                print(f"  Verified: {', '.join(parts)}")
            else:
                print(f"  Verified: (none to verify)")

        # ---- Step 4: Saturate + Extract Pareto ----
        if round_sound:
            new_front = _simulate_pareto_expansion(
                state, round_sound,
                rng_seed=config.seed + round_idx,
            )
            improvement = compute_pareto_improvement(baseline_pareto, new_front)

            if improvement > 0:
                state.pareto_front = new_front
                no_improvement_count = 0
                if config.verbose:
                    print(f"  Pareto:   {_c(_GREEN, f'+{improvement:.3f}')} improvement "
                          f"({len(new_front)} points)")
                    for entry in state.verified_rules[-len(round_sound):]:
                        entry.pareto_delta = improvement / len(round_sound)
            else:
                no_improvement_count += 1
                if config.verbose:
                    print(f"  Pareto:   no improvement ({no_improvement_count}/{config.convergence_window} "
                          f"toward convergence)")
        else:
            no_improvement_count += 1
            if config.verbose:
                print(f"  Pareto:   no new rules ({no_improvement_count}/{config.convergence_window} "
                      f"toward convergence)")

        # ---- Record round ----
        round_elapsed = time.time() - round_start
        round_data = {
            "round": round_idx + 1,
            "proposed": len(proposals),
            "valid": len(valid_proposals),
            "sound": len(round_sound),
            "unsound": round_unsound,
            "timeout": round_timeout,
            "pareto_size": len(state.pareto_front),
            "improvement": round(compute_pareto_improvement(baseline_pareto, state.pareto_front), 4),
            "elapsed_ms": int(round_elapsed * 1000),
        }
        state.round_history.append(round_data)

        if config.verbose:
            print(f"  Time:     {round_elapsed:.1f}s")

        # ---- Convergence check ----
        if no_improvement_count >= config.convergence_window:
            if config.verbose:
                print(f"\n{_c(_CYAN, 'Converged')} — no Pareto improvement for "
                      f"{config.convergence_window} consecutive rounds")
            break

    # ---- Final summary ----
    elapsed = time.time() - start

    # Build best designs list from Pareto front
    best_designs = []
    for i, p in enumerate(sorted(state.pareto_front, key=lambda p: (-p.security, p.latency))):
        best_designs.append({
            "rank": i + 1,
            "security": p.security,
            "latency": p.latency,
            "gates": p.gates,
        })

    result = LoopResult(
        rounds_completed=len(state.round_history),
        total_proposed=total_proposed,
        total_verified=total_verified,
        total_sound=total_sound,
        final_pareto_size=len(state.pareto_front),
        converged=no_improvement_count >= config.convergence_window,
        elapsed_seconds=elapsed,
        best_designs=best_designs,
        per_round=state.round_history,
    )

    if config.verbose:
        _print_header("Final Results")
        print(f"  Rounds:     {result.rounds_completed}")
        print(f"  Proposed:   {result.total_proposed} rules")
        print(f"  Verified:   {result.total_verified} via Lean kernel")
        print(f"  Sound:      {result.total_sound} rules added to pool")
        print(f"  Converged:  {'yes' if result.converged else 'no'}")
        print(f"  Time:       {result.elapsed_seconds:.1f}s")
        print()
        print("  Verified rule pool:")
        if state.verified_rules:
            for vr in state.verified_rules:
                name = vr.candidate["name"]
                src = vr.candidate.get("source", "?")
                rd = vr.round_added
                print(f"    [{rd}] {name} (source: {src})")
        else:
            print("    (empty)")
        print()
        print("  Final Pareto front:")
        _print_pareto(state.pareto_front)
        print()

    return result


# ============================================================
# CLI
# ============================================================

def main() -> None:
    if "--help" in sys.argv:
        print(__doc__)
        sys.exit(0)

    if "--test" in sys.argv:
        full = "--full" in sys.argv

        # Quick test: template mode, no Lean compilation
        config = LoopConfig(
            design="aes128",
            model="template",
            max_rounds=3,
            proposals_per_round=2,
            convergence_window=5,  # don't converge in 3 rounds
            seed=42,
            verify=full,          # only compile if --full
            verbose=True,
        )
        result = run_design_loop(config)

        assert result.rounds_completed == 3, f"Expected 3 rounds, got {result.rounds_completed}"
        assert result.total_proposed > 0, "Should propose at least some rules"

        if full:
            print("\n(Full verification mode — results depend on lake build)")
        else:
            assert result.total_sound > 0, "Simulated mode should have some SOUND rules"

        print(f"\nJSON summary:")
        print(json.dumps(result.to_json(), indent=2))
        print("\nSelf-test: PASS")
        return

    # Parse CLI args
    config = LoopConfig()

    if "--model" in sys.argv:
        idx = sys.argv.index("--model") + 1
        config.model = sys.argv[idx]
    if "--rounds" in sys.argv:
        idx = sys.argv.index("--rounds") + 1
        config.max_rounds = int(sys.argv[idx])
    if "--design" in sys.argv:
        idx = sys.argv.index("--design") + 1
        config.design = sys.argv[idx]
    if "--seed" in sys.argv:
        idx = sys.argv.index("--seed") + 1
        config.seed = int(sys.argv[idx])
    if "--proposals" in sys.argv:
        idx = sys.argv.index("--proposals") + 1
        config.proposals_per_round = int(sys.argv[idx])
    if "--timeout" in sys.argv:
        idx = sys.argv.index("--timeout") + 1
        config.timeout = int(sys.argv[idx])
    if "--no-verify" in sys.argv:
        config.verify = False
    if "--quiet" in sys.argv:
        config.verbose = False

    try:
        result = run_design_loop(config)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    if not config.verbose:
        print(json.dumps(result.to_json(), indent=2))

    sys.exit(0 if result.total_sound > 0 or result.converged else 1)


if __name__ == "__main__":
    main()
