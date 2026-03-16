import SuperHash

/-!
# Tests.Bridge — Hypothesis coupling bridge

Establishes formal coupling between Spec file theorems and the test suite.
Each `#check` ensures the theorem compiles and its type is accessible.
This file ensures that refactoring doesn't silently break Spec theorem signatures.

Only PUBLIC theorems are checked — private theorems are inaccessible from outside
their defining file.
-/

open SuperHash
open SuperHash.ILP

-- ============================================================
-- EGraph Core Spec (SuperHash/EGraph/CoreSpec.lean)
-- ============================================================

-- Hashcons operations
#check @hashcons_get?_insert_self
#check @hashcons_get?_insert_ne

-- Find preserves structure
#check @egraph_find_hashcons
#check @egraph_find_classes
#check @egraph_find_uf_size
#check @egraph_find_uf_wf
#check @egraph_find_preserves_roots
#check @egraph_find_preserves_isRootAt
#check @egraph_find_fst

-- Canonicalization
#check @isCanonical_of_no_children
#check @canonicalize_leaf
#check @canonicalize_hashcons
#check @canonicalize_classes
#check @canonicalize_uf_wf
#check @canonicalize_preserves_roots
#check @canonicalize_preserves_isRootAt
#check @canonicalize_uf_size
#check @canonicalize_output_bounded

-- Union-find push / root
#check @IsRootAt_of_push
#check @root_push_eq
#check @root_push_all_eq
#check @IsRootAt_of_rootD_self
#check @IsRootAt_backward_find

-- Empty graph well-formedness
#check @egraph_empty_wf

-- Add operations
#check @mem_singleton_nodes
#check @add_leaf_existing
#check @add_leaf_new
#check @add_leaf_preserves_wf
#check @add_existing_returns_id
#check @add_new_returns_fresh
#check @add_idempotent
#check @adds_leaf_preserve_wf
#check @add_preserves_uf_wf
#check @add_preserves_children_bounded
#check @add_preserves_hashcons_classes_aligned
#check @add_preserves_hashcons_entries_valid
#check @add_preserves_add_expr_inv
#check @add_id_bounded
#check @add_uf_size_ge

-- Merge operations
#check @merge_hashcons
#check @merge_uf_size
#check @eclass_union_mem
#check @merge_preserves_children_bounded
#check @merge_preserves_uf_wf
#check @merge_creates_equiv
#check @merge_preserves_equiv
#check @merge_post_invariant
#check @merge_preserves_uf_wf'
#check @merge_preserves_children_bounded'
#check @merge_preserves_pmi

-- Hashcons erase / rebuild
#check @hashcons_get?_erase_self
#check @hashcons_get?_erase_ne
#check @hashcons_get?_erase_insert_self
#check @hashcons_get?_erase_insert_ne

-- Rebuild / processClass
#check @processClass_classes
#check @processClass_uf_size
#check @processClass_preserves_roots
#check @processClass_preserves_pmi
#check @processClass_merges_bounded
#check @processClass_preserves_hcb

-- Rebuild pipeline
#check @mergeAll_preserves_pmi
#check @processAll_preserves_pmi
#check @clear_worklist_pmi
#check @rebuildStep_preserves_pmi

-- AddExprInv
#check @EGraphWF.toAddExprInv

-- ============================================================
-- Pipeline EMatch Spec (SuperHash/Pipeline/EMatchSpec.lean)
-- ============================================================

-- Pattern semantics
#check @sameShape_children_length
#check @sameShapeSemantics_holds
#check @Pattern.eval_patVar
#check @Pattern.eval_ext
#check @Pattern.map_eval_ext

-- Substitution
#check @zip_lookup_nodup
#check @Substitution.extend_some_get
#check @SubstExtends.refl
#check @SubstExtends.trans
#check @Substitution.extend_extends

-- Match soundness
#check @list_foldl_forall
#check @matchChildren_sound
#check @ematchF_sound_strong
#check @ematchF_sound
#check @pattern_rule_match_eq
#check @substVal_agrees
#check @InstantiateEvalSound_holds

-- Bounded substitution
#check @ematchF_substitution_bounded

-- Rule application soundness
#check @applyRuleAtF_sound

-- Saturation
#check @saturateF_preserves_consistent_internal

-- ============================================================
-- Pipeline ILP Spec (SuperHash/Pipeline/ILPSpec.lean)
-- ============================================================

-- Solution validation
#check @ILP.validSol_root_active
#check @ILP.checkRootActive_sound
#check @ILP.checkExactlyOne_sound
#check @ILP.checkChildDeps_sound
#check @ILP.checkAcyclicity_sound
#check @ILP.validSolution_decompose

-- ILP extraction correctness
#check @ILP.extractILP_correct
#check @ILP.ilp_extraction_soundness
#check @ILP.extractILP_fuel_mono
#check @ILP.mapOption_mono

-- ============================================================
-- Pipeline Completeness Spec (SuperHash/Pipeline/CompletenessSpec.lean)
-- ============================================================

-- Cost lower bound and acyclicity
#check @bestCostLowerBound_acyclic
#check @computeCostsF_bestCost_lower_bound
#check @computeCostsF_acyclic

-- Extraction completeness
#check @extractF_of_rank
#check @extractAuto_complete

-- ============================================================
-- Pipeline Soundness (SuperHash/Pipeline/Soundness.lean)
-- ============================================================

-- Helper: pattern rules preserve consistent valuation
#check @patternSoundRules_preserveCV

-- Well-formedness preservation
#check @saturateF_preserves_wf

-- End-to-end pipeline soundness
#check @optimizeF_soundness
#check @optimizeF_soundness_complete

-- ============================================================
-- Master Theorems (SuperHash/Pipeline/MasterTheorem.lean)
-- ============================================================

#check @pipeline_soundness
#check @pipeline_metrics_correct
#check @empty_pmi
#check @empty_bni

-- ============================================================
-- Master Theorem CS (SuperHash/Pipeline/MasterTheoremCS.lean)
-- ============================================================

#check @extractWeighted_correct_cs
#check @extractAll_correct_cs
#check @extractPareto_all_correct_cs
#check @superhash_pipeline_correct_crypto
#check @pipeline_soundness_crypto
#check @pipeline_metrics_correct_crypto

-- ============================================================
-- Master Theorem V2 (SuperHash/Pipeline/MasterTheoremV2.lean)
-- ============================================================

#check @designLoop_master
#check @designLoop_master_with_pattern_rules
