#!/usr/bin/env python3
"""
SuperHash v2.0 — Design Loop Orchestrator (N3.9)

Python Tier 1 orchestrator for the autonomous design loop:
  LLM proposes → Lean verifies → E-graph saturates → Pareto extracts → evaluate

MAP-Elites population management per CryptoConstruction island.
Evaluation cascade: fast syntax → compilation → spec_audit → Pareto improvement.
Convergence detection: stop when Pareto front stable for N rounds.

Usage:
  python3 scripts/design_loop.py --design aes --rounds 10 --seed 42
  python3 scripts/design_loop.py --test
"""

from __future__ import annotations

import json
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

sys.path.insert(0, str(Path(__file__).parent))

from rule_proposer import propose_rules, syntax_precheck, round_trip_validate
from rlvf_reward import ParetoPoint, compute_pareto_improvement, RewardBreakdown
from axle_integration import RuleCandidate, round_trip_check


# ============================================================
# MAP-Elites population
# ============================================================

@dataclass
class Island:
    """One island in the MAP-Elites population."""
    name: str  # CryptoConstruction family
    rules: list[dict] = field(default_factory=list)
    pareto_front: list[ParetoPoint] = field(default_factory=list)
    best_reward: float = 0.0


@dataclass
class Population:
    """MAP-Elites population across all islands."""
    islands: dict[str, Island] = field(default_factory=dict)

    def __post_init__(self):
        for family in ["SPN", "Feistel", "Sponge", "ARX"]:
            if family not in self.islands:
                self.islands[family] = Island(name=family)

    def total_rules(self) -> int:
        return sum(len(island.rules) for island in self.islands.values())


# ============================================================
# Loop configuration
# ============================================================

@dataclass
class LoopConfig:
    """Configuration for the design loop."""
    max_rounds: int = 10
    proposals_per_round: int = 5
    convergence_window: int = 3  # stop if no improvement for N rounds
    max_rules_per_island: int = 50
    seed: int = 42
    kill_switch_file: str = "/tmp/superhash_kill"  # V2-P6: kill switch


# ============================================================
# Design loop
# ============================================================

@dataclass
class LoopResult:
    """Result of the design loop execution."""
    rounds_completed: int
    total_rules_discovered: int
    final_pareto_size: int
    converged: bool
    elapsed_seconds: float
    per_round: list[dict] = field(default_factory=list)

    def to_json(self) -> dict:
        return {
            "rounds_completed": self.rounds_completed,
            "total_rules_discovered": self.total_rules_discovered,
            "final_pareto_size": self.final_pareto_size,
            "converged": self.converged,
            "elapsed_seconds": round(self.elapsed_seconds, 2),
            "per_round": self.per_round,
        }


def run_design_loop(
    config: LoopConfig,
    initial_pareto: Optional[list[ParetoPoint]] = None,
) -> LoopResult:
    """Run the autonomous design loop.

    Each round:
    1. Propose rules (template instantiation)
    2. Pre-check (syntax + round-trip)
    3. Compute reward (Pareto improvement)
    4. Update population

    Note: actual Lean compilation is skipped in this version.
    The loop demonstrates the orchestration pattern.
    """
    start = time.time()
    population = Population()

    if initial_pareto is None:
        initial_pareto = [ParetoPoint(100, 10, 50)]

    current_pareto = initial_pareto.copy()
    no_improvement_count = 0
    per_round_results = []

    for round_idx in range(config.max_rounds):
        # Kill switch check (V2-P6)
        if Path(config.kill_switch_file).exists():
            break

        round_start = time.time()

        # Step 1: Propose rules across all islands
        new_rules = 0
        for island_name in ["SPN", "Feistel", "Sponge", "ARX"]:
            proposals = propose_rules(
                island=island_name,
                count=config.proposals_per_round,
                base_seed=config.seed + round_idx * 100,
            )

            # Step 2: Pre-check
            valid = [p for p in proposals if syntax_precheck(p) and round_trip_validate(p)]

            # Step 3: Add to island (cap at max)
            island = population.islands[island_name]
            for p in valid:
                if len(island.rules) < config.max_rules_per_island:
                    island.rules.append(p)
                    new_rules += 1

        # Step 4: Simulate Pareto improvement (in real loop, this comes from Lean)
        if new_rules > 0:
            # Simulate: each new rule has a small chance of improving the front
            import random
            rng = random.Random(config.seed + round_idx)
            if rng.random() < 0.3:  # 30% chance of improvement per round
                new_point = ParetoPoint(
                    security=rng.randint(80, 150),
                    latency=rng.randint(5, 20),
                    gates=rng.randint(30, 80),
                )
                current_pareto.append(new_point)

        # Check improvement
        improvement = compute_pareto_improvement(initial_pareto, current_pareto)
        if improvement > 0:
            no_improvement_count = 0
        else:
            no_improvement_count += 1

        round_elapsed = time.time() - round_start
        per_round_results.append({
            "round": round_idx + 1,
            "new_rules": new_rules,
            "pareto_size": len(current_pareto),
            "improvement": round(improvement, 4),
            "elapsed_ms": int(round_elapsed * 1000),
        })

        # Convergence check
        if no_improvement_count >= config.convergence_window:
            break

    elapsed = time.time() - start
    return LoopResult(
        rounds_completed=len(per_round_results),
        total_rules_discovered=population.total_rules(),
        final_pareto_size=len(current_pareto),
        converged=no_improvement_count >= config.convergence_window,
        elapsed_seconds=elapsed,
        per_round=per_round_results,
    )


# ============================================================
# CLI
# ============================================================

def main() -> None:
    if "--help" in sys.argv:
        print(__doc__)
        sys.exit(0)

    if "--test" in sys.argv:
        config = LoopConfig(max_rounds=5, proposals_per_round=2, seed=42)
        result = run_design_loop(config)
        print(json.dumps(result.to_json(), indent=2))

        assert result.rounds_completed > 0
        assert result.total_rules_discovered > 0
        print(f"\nDesign loop: {result.rounds_completed} rounds, "
              f"{result.total_rules_discovered} rules, "
              f"{result.final_pareto_size} Pareto points")
        print("Self-test: PASS")
        return

    config = LoopConfig()
    if "--rounds" in sys.argv:
        idx = sys.argv.index("--rounds") + 1
        config.max_rounds = int(sys.argv[idx])
    if "--seed" in sys.argv:
        idx = sys.argv.index("--seed") + 1
        config.seed = int(sys.argv[idx])

    result = run_design_loop(config)
    print(json.dumps(result.to_json(), indent=2))


if __name__ == "__main__":
    main()
