═══ Specification Audit: superhash_lean ═══
Theorems: 613  Lemmas: 0  Pipeline: 39
Clean: 515  T1(vacuity): 1  T1.5(identity): 0  T2(weak): 9  T3(structural): 9  T4(no-witness): 79

── TIER 1 — VACUITY (1 issues) ──
  theorem zest_parallel_speedup
    SuperHash/Crypto/ExpanderBounds.lean:310
    ⚠ T1-UNUSED-ALL: all 1 parameters are _-prefixed — likely a stub or vacuous proof

── TIER 2 — WEAK SPECS (9 issues) ──
  theorem evalOp_ext_cs
    SuperHash/Crypto/CryptoNodeSemantics.lean:154
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_env']

  theorem round_reduce_safe
    SuperHash/Crypto/CryptoRule.lean:137
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_hr']

  theorem expander_collision_bound
    SuperHash/Crypto/ExpanderBounds.lean:94
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_h_coverage']

  theorem lp_security_mono
    SuperHash/Crypto/ExpanderBounds.lean:203
    ⚠ T2-UNUSED-PARTIAL: 1/2 params are _-prefixed: ['_h_calls']

  theorem expander_quantum_robustness
    SuperHash/Crypto/ExpanderBounds.lean:400
    ⚠ T2-UNUSED-PARTIAL: 1/2 params are _-prefixed: ['_h_grover']

  theorem coll_implies_sec
    SuperHash/Crypto/SecurityNotions.lean:119
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_h_coll']

  theorem coll_implies_eSec
    SuperHash/Crypto/SecurityNotions.lean:129
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_h_coll']

  theorem evalOp_ext_proof
    SuperHash/EGraph/Tests.lean:53
    ⚠ T2-UNUSED-PARTIAL: 1/3 params are _-prefixed: ['_env']

  theorem applyRuleAtF_sound [PIPELINE] [SORRY]
    SuperHash/Pipeline/EMatchSpec.lean:999
    ⚠ T2-PIPELINE-SORRY: pipeline theorem contains sorry — top-level result is unverified

── TIER 3 — STRUCTURAL (9 issues) ──
  theorem branch_spectral_bridge [PIPELINE]
    SuperHash/Crypto/ExpanderBounds.lean:124
    ⚠ T2-UNUSED-PARTIAL: 2/3 params are _-prefixed: ['_hbn', '_hd']
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem cryptosemantics_branch_spectral_bridge [PIPELINE]
    SuperHash/Crypto/ExpanderBounds.lean:146
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem bridge_is_ideal_bounded [PIPELINE]
    SuperHash/Crypto/SecurityNotions.lean:365
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem bridge_collision_le_diff [PIPELINE]
    SuperHash/Crypto/SecurityNotions.lean:382
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem bridge_collision_le_alg [PIPELINE]
    SuperHash/Crypto/SecurityNotions.lean:389
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem bridge_collision_le_birthday [PIPELINE]
    SuperHash/Crypto/SecurityNotions.lean:396
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)

  theorem pipeline_soundness [PIPELINE]
    SuperHash/Pipeline/MasterTheorem.lean:35
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary

  theorem patternSoundRules_preserveCV [PIPELINE]
    SuperHash/Pipeline/Soundness.lean:58
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

  theorem ConditionalSoundRewriteRule.isSound [PIPELINE]
    SuperHash/Rules/SoundRule.lean:87
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication

── TIER 4 — NO WITNESS (79 issues) ──
  theorem add_node_triple
    SuperHash/EGraph/AddNodeTriple.lean:17
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem consistent_root_eq
    SuperHash/EGraph/Consistency.lean:77
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem class_nodes_same_value
    SuperHash/EGraph/Consistency.lean:126
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem go_pairs_roots_sem
    SuperHash/EGraph/Consistency.lean:146
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem nodeEval_canonical
    SuperHash/EGraph/Consistency.lean:190
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merge_consistent
    SuperHash/EGraph/Consistency.lean:220
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem add_leaf_miss_consistent
    SuperHash/EGraph/Consistency.lean:349
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem add_leaf_hit_consistent
    SuperHash/EGraph/Consistency.lean:421
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem processClass_merges_semantically_valid
    SuperHash/EGraph/Consistency.lean:556
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem hca_cv_implies_shi
    SuperHash/EGraph/Consistency.lean:1095
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merge_preserves_shi
    SuperHash/EGraph/Consistency.lean:1124
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem processClass_shi_combined
    SuperHash/EGraph/Consistency.lean:1188
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rebuildStep_preserves_triple_aux
    SuperHash/EGraph/Consistency.lean:1374
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rebuildStepBody_preserves_triple
    SuperHash/EGraph/Consistency.lean:1411
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem IsRootAt_of_rootD_self
    SuperHash/EGraph/CoreSpec.lean:229
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem IsRootAt_backward_find
    SuperHash/EGraph/CoreSpec.lean:237
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem add_leaf_existing_wf
    SuperHash/EGraph/CoreSpec.lean:292
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem add_leaf_new_wf
    SuperHash/EGraph/CoreSpec.lean:337
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem merge_creates_equiv
    SuperHash/EGraph/CoreSpec.lean:615
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem go_output_bounded
    SuperHash/EGraph/CoreSpec.lean:1133
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem add_preserves_children_bounded
    SuperHash/EGraph/CoreSpec.lean:1283
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_push
    SuperHash/EGraph/UnionFind.lean:197
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_fuel_extra
    SuperHash/EGraph/UnionFind.lean:216
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_fuel_add
    SuperHash/EGraph/UnionFind.lean:270
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_bounded
    SuperHash/EGraph/UnionFind.lean:286
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem IsRootAt_set_ne
    SuperHash/EGraph/UnionFind.lean:300
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_parent_step
    SuperHash/EGraph/UnionFind.lean:312
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_not_in_class
    SuperHash/EGraph/UnionFind.lean:327
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_other_class
    SuperHash/EGraph/UnionFind.lean:355
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_same_class
    SuperHash/EGraph/UnionFind.lean:382
    ⚠ T2-UNUSED-PARTIAL: 3/7 params are _-prefixed: ['_hbnd', '_hacyc', '_hrt_eq']
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_to_root
    SuperHash/EGraph/UnionFind.lean:444
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem compressPath_preserves_rootD
    SuperHash/EGraph/UnionFind.lean:460
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem compressPath_bounded
    SuperHash/EGraph/UnionFind.lean:551
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem root_setIfInBounds_target
    SuperHash/EGraph/UnionFind.lean:666
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_avoids_root
    SuperHash/EGraph/UnionFind.lean:698
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_compose
    SuperHash/EGraph/UnionFind.lean:727
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_union_step
    SuperHash/EGraph/UnionFind.lean:746
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem cycle_contradicts_wf
    SuperHash/EGraph/UnionFind.lean:842
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_depth_bound
    SuperHash/EGraph/UnionFind.lean:861
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_root_to_root
    SuperHash/EGraph/UnionFind.lean:894
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rootD_set_root_to_oob
    SuperHash/EGraph/UnionFind.lean:909
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem union_creates_equiv
    SuperHash/EGraph/UnionFind.lean:924
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem union_root_cases
    SuperHash/EGraph/UnionFind.lean:1162
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractWeighted_correct [PIPELINE]
    SuperHash/Pareto/Extract.lean:111
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractAll_correct [PIPELINE]
    SuperHash/Pareto/Extract.lean:125
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractPareto_all_correct [PIPELINE]
    SuperHash/Pareto/Soundness.lean:94
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractF_of_rank
    SuperHash/Pipeline/CompletenessSpec.lean:365
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractAuto_complete
    SuperHash/Pipeline/CompletenessSpec.lean:410
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem zip_lookup_nodup
    SuperHash/Pipeline/EMatchSpec.lean:175
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem matchChildren_sound [PIPELINE]
    SuperHash/Pipeline/EMatchSpec.lean:263
    ⚠ T2-UNUSED-PARTIAL: 2/17 params are _-prefixed: ['_hcv', '_hwf']
    ⚠ T3-MANY-HYPOTHESES: 17 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ematchF_sound_strong [PIPELINE]
    SuperHash/Pipeline/EMatchSpec.lean:349
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ematchF_sound [PIPELINE]
    SuperHash/Pipeline/EMatchSpec.lean:453
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem pattern_rule_match_eq
    SuperHash/Pipeline/EMatchSpec.lean:490
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem substVal_agrees
    SuperHash/Pipeline/EMatchSpec.lean:532
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem instantiateF_go_sound [PIPELINE]
    SuperHash/Pipeline/EMatchSpec.lean:556
    ⚠ T3-MANY-HYPOTHESES: 28 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 13 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extend_preserves_bounded
    SuperHash/Pipeline/EMatchSpec.lean:767
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem ematch_value_chain
    SuperHash/Pipeline/EMatchSpec.lean:873
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem saturateF_preserves_consistent_internal
    SuperHash/Pipeline/EMatchSpec.lean:1098
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem mapOption_get
    SuperHash/Pipeline/Extract.lean:64
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractF_correct [PIPELINE]
    SuperHash/Pipeline/Extract.lean:200
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem extractAuto_correct [PIPELINE]
    SuperHash/Pipeline/Extract.lean:246
    ⚠ T3-MANY-HYPOTHESES: 10 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem computeCostsF_extractF_correct [PIPELINE]
    SuperHash/Pipeline/Extract.lean:263
    ⚠ T3-MANY-HYPOTHESES: 13 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem superhash_pipeline_correct [PIPELINE]
    SuperHash/Pipeline/Integration.lean:56
    ⚠ T3-MANY-HYPOTHESES: 13 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem instantiateF_go_preserves_addExprInv
    SuperHash/Pipeline/Saturate.lean:93
    ⚠ T2-UNUSED-PARTIAL: 2/13 params are _-prefixed: ['_inv0', '_h_s0']
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem instantiateF_go_preserves_consistency
    SuperHash/Pipeline/Saturate.lean:186
    ⚠ T2-UNUSED-PARTIAL: 6/23 params are _-prefixed: ['_hrc', '_hv0', '_inv0', '_h_s0', '_inv0', '_h_s0']
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem instantiateF_preserves_consistency
    SuperHash/Pipeline/Saturate.lean:233
    ⚠ T4-NO-WITNESS: 3 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem foldl_preserves_cv
    SuperHash/Pipeline/Saturate.lean:388
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rebuildStepBody_preserves_cv
    SuperHash/Pipeline/Saturate.lean:458
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem rebuildF_preserves_cv
    SuperHash/Pipeline/Saturate.lean:470
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem applyRulesF_preserves_cv
    SuperHash/Pipeline/Saturate.lean:490
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem saturateF_preserves_consistent
    SuperHash/Pipeline/Saturate.lean:507
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem saturateF_preserves_quadruple
    SuperHash/Pipeline/Saturate.lean:747
    ⚠ T2-EXISTENTIAL-ONLY: conclusion is existential without equality/equivalence — may not reach concrete evaluation
    ⚠ T4-NO-WITNESS: 5 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem saturateF_preserves_wf
    SuperHash/Pipeline/Soundness.lean:121
    ⚠ T4-NO-WITNESS: 4 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem optimizeF_soundness [PIPELINE]
    SuperHash/Pipeline/Soundness.lean:146
    ⚠ T3-MANY-HYPOTHESES: 16 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 8 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem optimizeF_soundness_complete [PIPELINE]
    SuperHash/Pipeline/Soundness.lean:200
    ⚠ T3-MANY-HYPOTHESES: 15 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem sound_rule_preserves_consistency [PIPELINE]
    SuperHash/Rules/SoundRule.lean:104
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication
    ⚠ T3-MANY-HYPOTHESES: 11 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem conditional_sound_rule_preserves_consistency [PIPELINE]
    SuperHash/Rules/SoundRule.lean:118
    ⚠ T3-NAME-MISMATCH: name contains 'sound' but conclusion has no equality, biconditional, or implication
    ⚠ T3-MANY-HYPOTHESES: 12 hypotheses on pipeline theorem — verify each is satisfiable and necessary
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses [pipeline, threshold=2] but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem equivalence_rule_preserves_consistency
    SuperHash/Rules/SoundRule.lean:147
    ⚠ T3-DIRECTION: name suggests equivalence but conclusion is unidirectional (→ not ↔)
    ⚠ T4-NO-WITNESS: 6 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

  theorem improvement_rule_preserves_consistency
    SuperHash/Rules/SoundRule.lean:160
    ⚠ T4-NO-WITNESS: 7 Prop hypotheses but no non-vacuity example found in Tests/NonVacuity*.lean or same file

✗ FAIL — Blocking spec issues detected (Tier 1 vacuity or pipeline sorry)