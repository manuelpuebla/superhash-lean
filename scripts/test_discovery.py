#!/usr/bin/env python3
"""
SuperHash v2.0 — Rule Discovery Integration Test (N2.8)

End-to-end test of the rule discovery pipeline:
  1. LLM proposes rules (via templates)
  2. Pre-check filters obviously bad rules
  3. AXLE verifies candidates via Lean kernel
  4. Verified rules added to pool
  5. RLVF reward computed

Usage:
  python3 scripts/test_discovery.py
  python3 scripts/test_discovery.py --full  # includes compilation (slow)
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

# Add scripts directory to path
sys.path.insert(0, str(Path(__file__).parent))

from axle_integration import RuleCandidate, round_trip_check, VerificationResult
from rlvf_reward import (
    RewardConfig, compute_pareto_improvement, ParetoPoint,
    check_syntax, RewardBreakdown,
)
from rule_proposer import (
    propose_rules, syntax_precheck, round_trip_validate,
    SEED_TEMPLATES,
)
from proving_pipeline import (
    PipelineResult, ProofAttempt, ProverLayer, ProofResult, treefinement,
)


def test_rule_proposer() -> bool:
    """Test rule proposal engine."""
    print("=== Test: Rule Proposer ===")

    # Test per-island proposal
    for island in ["SPN", "Feistel", "Sponge", "ARX"]:
        proposals = propose_rules(island=island, count=3)
        assert len(proposals) > 0, f"No proposals for island {island}"
        for p in proposals:
            assert syntax_precheck(p), f"Bad syntax: {p['name']}"
            assert round_trip_validate(p), f"Round-trip fail: {p['name']}"

    # Test all islands
    all_proposals = propose_rules(count=2)
    assert len(all_proposals) == 10, f"Expected 10, got {len(all_proposals)}"

    print(f"  Generated {len(all_proposals)} proposals across 5 templates")
    print("  PASS")
    return True


def test_round_trip_validation() -> bool:
    """Test TCB round-trip validation (D11)."""
    print("=== Test: TCB Round-Trip (D11) ===")

    good = RuleCandidate(
        name="test_good",
        classification="equivalence",
        lhs_template=".iterate 1 (.var 0)",
        rhs_template=".var 0",
        source="test",
    )
    assert round_trip_check(good), "Good rule round-trip failed"

    # Test with all fields
    full = RuleCandidate(
        name="test_full",
        classification="conditional",
        lhs_template=".sbox 7 (.var 0)",
        rhs_template=".sbox 5 (.var 0)",
        side_condition="deg(s2) >= deg(s1)",
        source="llm_gpt4",
        confidence=75,
    )
    assert round_trip_check(full), "Full rule round-trip failed"

    print("  All round-trip checks passed")
    print("  PASS")
    return True


def test_rlvf_reward() -> bool:
    """Test RLVF reward computation."""
    print("=== Test: RLVF Reward Model ===")

    config = RewardConfig()
    assert abs(config.max_reward - 1.0) < 0.01, f"Max reward: {config.max_reward}"

    # Test Pareto improvement
    baseline = [ParetoPoint(100, 10, 50), ParetoPoint(120, 12, 60)]
    improved = baseline + [ParetoPoint(110, 9, 45)]  # new non-dominated
    no_change = baseline.copy()

    score_improved = compute_pareto_improvement(baseline, improved)
    score_same = compute_pareto_improvement(baseline, no_change)

    assert score_improved > 0, f"Should detect improvement: {score_improved}"
    assert score_same == 0, f"Should detect no change: {score_same}"

    # Test dominance
    assert ParetoPoint(100, 10, 50).dominates(ParetoPoint(90, 11, 55))
    assert not ParetoPoint(100, 10, 50).dominates(ParetoPoint(110, 9, 45))

    print(f"  Pareto improvement: {score_improved:.3f} (expected > 0)")
    print(f"  No-change score: {score_same:.3f} (expected 0)")
    print("  PASS")
    return True


def test_proving_pipeline() -> bool:
    """Test proving pipeline structure."""
    print("=== Test: Proving Pipeline ===")

    # Test pipeline result serialization
    result = PipelineResult(
        success=True,
        winning_layer=ProverLayer.AXLE,
        attempts=[
            ProofAttempt(ProverLayer.AXLE, ProofResult.SUCCESS, 50, tactic="simp"),
        ],
        total_elapsed_ms=50,
    )
    j = result.to_json()
    assert j["success"] is True
    assert j["winning_layer"] == "axle"
    assert len(j["attempts"]) == 1

    # Test treefinement
    refined = treefinement("simp made no progress", "goal")
    assert refined is not None

    refined2 = treefinement("unknown error xyz", "goal")
    assert refined2 is None  # no suggestion for unknown errors

    print("  Pipeline result serialization: OK")
    print("  Treefinement: OK")
    print("  PASS")
    return True


def test_integration_flow() -> bool:
    """Test the full integration flow (without compilation)."""
    print("=== Test: Integration Flow ===")

    # Step 1: Propose rules
    proposals = propose_rules(island="SPN", count=3)
    print(f"  Step 1: {len(proposals)} rules proposed")

    # Step 2: Pre-check
    valid = [p for p in proposals if syntax_precheck(p)]
    print(f"  Step 2: {len(valid)}/{len(proposals)} passed pre-check")

    # Step 3: Round-trip validation
    validated = [p for p in valid if round_trip_validate(p)]
    print(f"  Step 3: {len(validated)}/{len(valid)} passed round-trip")

    # Step 4: Pareto baseline
    baseline = [ParetoPoint(100, 10, 50)]
    print(f"  Step 4: Baseline Pareto front: {len(baseline)} points")

    # Step 5: Simulated reward
    reward = RewardBreakdown(
        level0_syntax=0.1,  # passed syntax
        level1_compile=0.0,  # not compiled in this test
        level2_nonvacuity=0.0,
        level3_pareto=0.0,
    )
    print(f"  Step 5: Reward = {reward.total:.2f} (syntax only, no compilation)")

    assert len(validated) > 0, "Should have at least 1 valid proposal"
    print("  PASS")
    return True


def main() -> None:
    if "--help" in sys.argv:
        print(__doc__)
        sys.exit(0)

    print("SuperHash v2.0 — Rule Discovery Integration Test\n")

    results = []
    results.append(("Rule Proposer", test_rule_proposer()))
    results.append(("TCB Round-Trip", test_round_trip_validation()))
    results.append(("RLVF Reward", test_rlvf_reward()))
    results.append(("Proving Pipeline", test_proving_pipeline()))
    results.append(("Integration Flow", test_integration_flow()))

    print("\n" + "=" * 50)
    all_pass = all(r for _, r in results)
    for name, passed in results:
        status = "PASS" if passed else "FAIL"
        print(f"  {name}: {status}")

    print(f"\nOverall: {'ALL PASS' if all_pass else 'SOME FAILED'}")
    sys.exit(0 if all_pass else 1)


if __name__ == "__main__":
    main()
