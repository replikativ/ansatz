import Mathlib

-- E0 Lean baseline: for each sampled theorem, try aesop (real baseline;
-- no self-access) and exact? (expected self-hit; recall-pipeline sanity).
-- Generated from bench/results/e0-sample.edn — parse results by line.

-- #0 aesop Primrec.to₂
example : type_of% @Primrec.to₂ := by aesop
-- #0 exact? Primrec.to₂
example : type_of% @Primrec.to₂ := by exact?

-- #1 aesop List.foldlM_pure
example : type_of% @List.foldlM_pure := by aesop
-- #1 exact? List.foldlM_pure
example : type_of% @List.foldlM_pure := by exact?

-- #2 aesop CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument'
example : type_of% @CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument' := by aesop
-- #2 exact? CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument'
example : type_of% @CategoryTheory.MorphismProperty.llp_rlp_of_hasSmallObjectArgument' := by exact?

-- #3 aesop Lean.Grind.Ring.intCast_mul_left_comm
example : type_of% @Lean.Grind.Ring.intCast_mul_left_comm := by aesop
-- #3 exact? Lean.Grind.Ring.intCast_mul_left_comm
example : type_of% @Lean.Grind.Ring.intCast_mul_left_comm := by exact?

-- #4 aesop WeierstrassCurve.Projective.equation_zero
example : type_of% @WeierstrassCurve.Projective.equation_zero := by aesop
-- #4 exact? WeierstrassCurve.Projective.equation_zero
example : type_of% @WeierstrassCurve.Projective.equation_zero := by exact?

-- #5 aesop Std.DTreeMap.Raw.getKey?_diff_of_mem_right
example : type_of% @Std.DTreeMap.Raw.getKey?_diff_of_mem_right := by aesop
-- #5 exact? Std.DTreeMap.Raw.getKey?_diff_of_mem_right
example : type_of% @Std.DTreeMap.Raw.getKey?_diff_of_mem_right := by exact?

-- #6 aesop CategoryTheory.Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations
example : type_of% @CategoryTheory.Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations := by aesop
-- #6 exact? CategoryTheory.Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations
example : type_of% @CategoryTheory.Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations := by exact?

-- #7 aesop Nat.minFac_eq_two_iff
example : type_of% @Nat.minFac_eq_two_iff := by aesop
-- #7 exact? Nat.minFac_eq_two_iff
example : type_of% @Nat.minFac_eq_two_iff := by exact?

-- #8 aesop Std.DHashMap.Internal.toListModel_replicate_nil
example : type_of% @Std.DHashMap.Internal.toListModel_replicate_nil := by aesop
-- #8 exact? Std.DHashMap.Internal.toListModel_replicate_nil
example : type_of% @Std.DHashMap.Internal.toListModel_replicate_nil := by exact?

-- #9 aesop List.prefix_concat
example : type_of% @List.prefix_concat := by aesop
-- #9 exact? List.prefix_concat
example : type_of% @List.prefix_concat := by exact?

-- #10 aesop IsSemisimpleRing.jacobson_eq_bot
example : type_of% @IsSemisimpleRing.jacobson_eq_bot := by aesop
-- #10 exact? IsSemisimpleRing.jacobson_eq_bot
example : type_of% @IsSemisimpleRing.jacobson_eq_bot := by exact?

-- #11 aesop Std.Sat.AIG.instLawfulOperatorBinaryInputMkOrCached
example : type_of% @Std.Sat.AIG.instLawfulOperatorBinaryInputMkOrCached := by aesop
-- #11 exact? Std.Sat.AIG.instLawfulOperatorBinaryInputMkOrCached
example : type_of% @Std.Sat.AIG.instLawfulOperatorBinaryInputMkOrCached := by exact?

-- #12 aesop tendsto_inv_nhdsLT
example : type_of% @tendsto_inv_nhdsLT := by aesop
-- #12 exact? tendsto_inv_nhdsLT
example : type_of% @tendsto_inv_nhdsLT := by exact?

-- #13 aesop Subalgebra.add_mem
example : type_of% @Subalgebra.add_mem := by aesop
-- #13 exact? Subalgebra.add_mem
example : type_of% @Subalgebra.add_mem := by exact?

-- #14 aesop instIsEmptyFalse
example : type_of% @instIsEmptyFalse := by aesop
-- #14 exact? instIsEmptyFalse
example : type_of% @instIsEmptyFalse := by exact?

-- #15 aesop CategoryTheory.reflectsColimitsOfCreatesColimits
example : type_of% @CategoryTheory.reflectsColimitsOfCreatesColimits := by aesop
-- #15 exact? CategoryTheory.reflectsColimitsOfCreatesColimits
example : type_of% @CategoryTheory.reflectsColimitsOfCreatesColimits := by exact?

-- #16 aesop nhdsGE_basis_of_exists_gt
example : type_of% @nhdsGE_basis_of_exists_gt := by aesop
-- #16 exact? nhdsGE_basis_of_exists_gt
example : type_of% @nhdsGE_basis_of_exists_gt := by exact?

-- #17 aesop Filter.Tendsto.isCoboundedUnder_ge
example : type_of% @Filter.Tendsto.isCoboundedUnder_ge := by aesop
-- #17 exact? Filter.Tendsto.isCoboundedUnder_ge
example : type_of% @Filter.Tendsto.isCoboundedUnder_ge := by exact?

-- #18 aesop MulChar.injective_ringHomComp
example : type_of% @MulChar.injective_ringHomComp := by aesop
-- #18 exact? MulChar.injective_ringHomComp
example : type_of% @MulChar.injective_ringHomComp := by exact?

-- #19 aesop ENNReal.lt_add_of_sub_lt_left
example : type_of% @ENNReal.lt_add_of_sub_lt_left := by aesop
-- #19 exact? ENNReal.lt_add_of_sub_lt_left
example : type_of% @ENNReal.lt_add_of_sub_lt_left := by exact?

-- #20 aesop TopologicalSpace.Compacts.coe_bot
example : type_of% @TopologicalSpace.Compacts.coe_bot := by aesop
-- #20 exact? TopologicalSpace.Compacts.coe_bot
example : type_of% @TopologicalSpace.Compacts.coe_bot := by exact?

-- #21 aesop Nat.Linear.Poly.denote_le_cancel
example : type_of% @Nat.Linear.Poly.denote_le_cancel := by aesop
-- #21 exact? Nat.Linear.Poly.denote_le_cancel
example : type_of% @Nat.Linear.Poly.denote_le_cancel := by exact?

-- #22 aesop Algebra.IsStandardSmoothOfRelativeDimension.id
example : type_of% @Algebra.IsStandardSmoothOfRelativeDimension.id := by aesop
-- #22 exact? Algebra.IsStandardSmoothOfRelativeDimension.id
example : type_of% @Algebra.IsStandardSmoothOfRelativeDimension.id := by exact?

-- #23 aesop Commute.units_inv_left_iff
example : type_of% @Commute.units_inv_left_iff := by aesop
-- #23 exact? Commute.units_inv_left_iff
example : type_of% @Commute.units_inv_left_iff := by exact?

-- #24 aesop subset_closedConvexHull
example : type_of% @subset_closedConvexHull := by aesop
-- #24 exact? subset_closedConvexHull
example : type_of% @subset_closedConvexHull := by exact?

-- #25 aesop SupPrime.le_finset_sup
example : type_of% @SupPrime.le_finset_sup := by aesop
-- #25 exact? SupPrime.le_finset_sup
example : type_of% @SupPrime.le_finset_sup := by exact?

-- #26 aesop NNReal.coe_lt_one
example : type_of% @NNReal.coe_lt_one := by aesop
-- #26 exact? NNReal.coe_lt_one
example : type_of% @NNReal.coe_lt_one := by exact?

-- #27 aesop Num.add_of_nat
example : type_of% @Num.add_of_nat := by aesop
-- #27 exact? Num.add_of_nat
example : type_of% @Num.add_of_nat := by exact?

-- #28 aesop Nat.cast_ofNat
example : type_of% @Nat.cast_ofNat := by aesop
-- #28 exact? Nat.cast_ofNat
example : type_of% @Nat.cast_ofNat := by exact?

-- #29 aesop Rat.floor_def
example : type_of% @Rat.floor_def := by aesop
-- #29 exact? Rat.floor_def
example : type_of% @Rat.floor_def := by exact?

-- #30 aesop Array.back?_attach
example : type_of% @Array.back?_attach := by aesop
-- #30 exact? Array.back?_attach
example : type_of% @Array.back?_attach := by exact?

-- #31 aesop Nat.not_dvd_iff_lt_mul_succ
example : type_of% @Nat.not_dvd_iff_lt_mul_succ := by aesop
-- #31 exact? Nat.not_dvd_iff_lt_mul_succ
example : type_of% @Nat.not_dvd_iff_lt_mul_succ := by exact?

-- #32 aesop MeasureTheory.stoppedProcess_eq_of_le
example : type_of% @MeasureTheory.stoppedProcess_eq_of_le := by aesop
-- #32 exact? MeasureTheory.stoppedProcess_eq_of_le
example : type_of% @MeasureTheory.stoppedProcess_eq_of_le := by exact?

-- #33 aesop Polynomial.Separable.mul
example : type_of% @Polynomial.Separable.mul := by aesop
-- #33 exact? Polynomial.Separable.mul
example : type_of% @Polynomial.Separable.mul := by exact?

-- #34 aesop CategoryTheory.Discrete.opposite_functor_obj_as
example : type_of% @CategoryTheory.Discrete.opposite_functor_obj_as := by aesop
-- #34 exact? CategoryTheory.Discrete.opposite_functor_obj_as
example : type_of% @CategoryTheory.Discrete.opposite_functor_obj_as := by exact?

-- #35 aesop Set.mem_Ioi
example : type_of% @Set.mem_Ioi := by aesop
-- #35 exact? Set.mem_Ioi
example : type_of% @Set.mem_Ioi := by exact?

-- #36 aesop MeasureTheory.integral_indicator₂
example : type_of% @MeasureTheory.integral_indicator₂ := by aesop
-- #36 exact? MeasureTheory.integral_indicator₂
example : type_of% @MeasureTheory.integral_indicator₂ := by exact?

-- #37 aesop Multiset.coe_add
example : type_of% @Multiset.coe_add := by aesop
-- #37 exact? Multiset.coe_add
example : type_of% @Multiset.coe_add := by exact?

-- #38 aesop HomologicalComplex.instIsStableUnderRetractsQuasiIso
example : type_of% @HomologicalComplex.instIsStableUnderRetractsQuasiIso := by aesop
-- #38 exact? HomologicalComplex.instIsStableUnderRetractsQuasiIso
example : type_of% @HomologicalComplex.instIsStableUnderRetractsQuasiIso := by exact?

-- #39 aesop Nat.instStarOrderedRing
example : type_of% @Nat.instStarOrderedRing := by aesop
-- #39 exact? Nat.instStarOrderedRing
example : type_of% @Nat.instStarOrderedRing := by exact?

-- #40 aesop AddCommute.list_sum_right
example : type_of% @AddCommute.list_sum_right := by aesop
-- #40 exact? AddCommute.list_sum_right
example : type_of% @AddCommute.list_sum_right := by exact?

-- #41 aesop Ordering.lt_beq_eq
example : type_of% @Ordering.lt_beq_eq := by aesop
-- #41 exact? Ordering.lt_beq_eq
example : type_of% @Ordering.lt_beq_eq := by exact?

-- #42 aesop MeasurableEquiv.symm_symm
example : type_of% @MeasurableEquiv.symm_symm := by aesop
-- #42 exact? MeasurableEquiv.symm_symm
example : type_of% @MeasurableEquiv.symm_symm := by exact?

-- #43 aesop Set.subset_range_of_surjective
example : type_of% @Set.subset_range_of_surjective := by aesop
-- #43 exact? Set.subset_range_of_surjective
example : type_of% @Set.subset_range_of_surjective := by exact?

-- #44 aesop Disjoint.of_image
example : type_of% @Disjoint.of_image := by aesop
-- #44 exact? Disjoint.of_image
example : type_of% @Disjoint.of_image := by exact?

-- #45 aesop uniformity_basis_edist_nnreal
example : type_of% @uniformity_basis_edist_nnreal := by aesop
-- #45 exact? uniformity_basis_edist_nnreal
example : type_of% @uniformity_basis_edist_nnreal := by exact?

-- #46 aesop Nat.two_mul_sq_add_one_le_two_pow_two_mul
example : type_of% @Nat.two_mul_sq_add_one_le_two_pow_two_mul := by aesop
-- #46 exact? Nat.two_mul_sq_add_one_le_two_pow_two_mul
example : type_of% @Nat.two_mul_sq_add_one_le_two_pow_two_mul := by exact?

-- #47 aesop Cardinal.lift_mk_shrink''
example : type_of% @Cardinal.lift_mk_shrink'' := by aesop
-- #47 exact? Cardinal.lift_mk_shrink''
example : type_of% @Cardinal.lift_mk_shrink'' := by exact?

-- #48 aesop GenContFract.IntFractPair.succ_nth_stream_eq_some_iff
example : type_of% @GenContFract.IntFractPair.succ_nth_stream_eq_some_iff := by aesop
-- #48 exact? GenContFract.IntFractPair.succ_nth_stream_eq_some_iff
example : type_of% @GenContFract.IntFractPair.succ_nth_stream_eq_some_iff := by exact?

-- #49 aesop ProbabilityTheory.isProbabilityMeasureGamma
example : type_of% @ProbabilityTheory.isProbabilityMeasureGamma := by aesop
-- #49 exact? ProbabilityTheory.isProbabilityMeasureGamma
example : type_of% @ProbabilityTheory.isProbabilityMeasureGamma := by exact?

