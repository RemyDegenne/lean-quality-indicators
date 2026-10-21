# unnecessary-hypotheses: run `main`, judge `gpt-6.1-sol-high-repeat-2`

| Library | Sampled | Judged | Flagged | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|
| Mathlib | 1000 | 300 | 12 | 4.0% | 2.3%–6.9% | unknown |
| Tau Ceti | 1000 | 300 | 18 | 6.0% | 3.8%–9.3% | unknown |
| Lean Pool | 1000 | 300 | 61 | 20.3% | 16.2%–25.2% | unknown |
| FLT (Anthropic) | 1000 | 300 | 79 | 26.3% | 21.7%–31.6% | unknown |
| Formal Frontier | 1000 | 300 | 17 | 5.7% | 3.6%–8.9% | unknown |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (12 flagged)

### [`RatFunc.Luroth.Φ_natDegree_eq_φ_natDegree`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/RatFunc/Luroth.lean#L182-L185) — `mathlib-0077`

Snippet: `samples/mathlib/mathlib-0077.lean`

- `(h : E ≠ ⊥)` (theorem): Use Polynomial.natDegree_primPart to reduce to (Φ' E).natDegree. Mapping injectively into K⟮X⟯ preserves natDegree, and Φ'_map identifies the mapped polynomial with (b E) • (φ E).map (algebraMap E K⟮X⟯). The scalar is nonzero by b_ne_zero and algebraMap_injective, so Polynomial.natDegree_smul and Polynomial.natDegree_map finish without h. This also covers φ E = 0: integerNormalization_eq_zero_iff gives Φ' E = 0, whose primitive part is 1; both sides then have natDegree 0.

### [`Module.Basis.toMatrix_mulVec_repr`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Matrix/Basis.lean#L231-L236) — `mathlib-0083`

Snippet: `samples/mathlib/mathlib-0083.lean`

- `[Finite ι']` (theorem): Only the column index ι needs finiteness. After deleting this binder, apply function extensionality at i; unfolding Matrix.mulVec_apply_eq_sum and Basis.toMatrix_apply reduces the goal to b'.sum_repr_mul_repr b m i (Mathlib/LinearAlgebra/Basis/Defs.lean:641). This lemma requires Fintype ι but no finiteness of ι'. It also covers empty index types and trivial semirings.

### [`MeasureTheory.projectiveFamilyContent_mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean#L134-L137) — `mathlib-0116`

Snippet: `samples/mathlib/mathlib-0116.lean`

- `(hs : s ∈ measurableCylinders α)` (theorem): Split on whether s belongs to measurableCylinders α. If so, the existing addContent_mono proof applies. Otherwise, projectiveFamilyContent_eq and the definition of projectiveFamilyFun give projectiveFamilyContent hP s = 0, so nonnegativity proves the inequality. This also handles empty or trivial underlying types without additional assumptions.

### [`WeierstrassCurve.preΨ_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean#L314-L318) — `mathlib-0123`

Snippet: `samples/mathlib/mathlib-0123.lean`

- `[Nontrivial R]` (theorem): The remaining hypothesis h already implies Nontrivial R via `nontrivial_of_ne (n : R) 0 h` (Mathlib/Basic/Nontrivial/Defs.lean). Delete the binder, prepend `letI : Nontrivial R := nontrivial_of_ne (n : R) 0 h`, and retain the original proof. In a trivial ring h is impossible, so that case is covered.

### [`AdicCompletion.tensor_map_id_left_injective_of_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean#L367-L373) — `mathlib-0139`

Snippet: `samples/mathlib/mathlib-0139.lean`

- `[Module.Finite R M]` (variable): The remaining assumptions imply IsNoetherian R N via isNoetherian_of_isNoetherianRing_of_finite. Then Module.Finite.of_injective f hf supplies Module.Finite R M locally, and the original proof applies. This also covers trivial modules and the zero ring.
- `[Module.Finite R N]` (variable): AdicCompletion.flat_of_isNoetherian gives flatness without either module-finiteness assumption. Module.Flat.lTensor_preserves_injective_linearMap f hf then proves the conclusion: AlgebraTensorModule.coe_lTensor identifies its underlying function with the displayed map. To avoid circularity with the later flatness instance, retain the original finite-case proof as an auxiliary lemma, derive flatness exactly as in that instance, then prove this result. Both finiteness hypotheses can be removed together; flatness preservation includes trivial modules and the zero ring.

### [`Convex.norm_image_sub_le_of_norm_fderiv_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/MeanValue.lean#L498-L504) — `mathlib-0148`

Snippet: `samples/mathlib/mathlib-0148.lean`

- `[IsRCLikeNormedField 𝕜]` (variable): The statement elaborates without this instance. A proof can avoid restricting scalars: hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff, and ContinuousLinearMap.le_of_opNorm_le give, at each z ∈ s and for every ε > 0, the local estimate ‖f w - f z‖ ≤ (C + ε) * ‖w - z‖. Set p(t) = x + t • (y - x), D = ‖y - x‖, and q(t) = ‖f (p(t)) - f x‖. Convexity keeps p([0,1]) in s, and differentiability makes q continuous there. The local estimate and the triangle inequality show that, for every r > C * D, the right slope of q is eventually less than r. Apply image_le_of_liminf_slope_right_le_deriv_boundary with B(t) = C * D * t to obtain q(1) ≤ C * D. If D = 0, then y = x and the conclusion is immediate. Empty s is excluded by xs; trivial spaces cause no difficulty, and bound at x ensures C ≥ 0. No real or complex structure on 𝕜 is used.

### [`continuous_parametric_integral_of_continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/Bochner/Set.lean#L1121-L1139) — `mathlib-0190`

Snippet: `samples/mathlib/mathlib-0190.lean`

- `[FirstCountableTopology X]` (theorem): Replace dominated convergence with an epsilon estimate. Compactness gives integrability of every slice on s. IsCompact.mem_uniformity_of_prod gives, near x₀, a uniform bound ‖f x y - f x₀ y‖ ≤ δ for y ∈ s, without countability assumptions on X. Using integral_sub and norm_setIntegral_le_of_norm_le_const bounds the difference of integrals by δ * μ.real s. Choose δ = ε / (μ.real s + 1). This also covers zero measure and empty s; empty X is vacuous. Local compactness is unnecessary for this argument too.
- `[LocallyCompactSpace X]` (theorem): Keep the dominated-convergence argument, but replace the compact neighborhood U. Compactness bounds ‖f x₀ y‖ on s by some M. IsCompact.mem_uniformity_of_prod, applied with distance less than 1, supplies a neighborhood V of x₀ where ‖f x y‖ ≤ M + 1 for every y ∈ s. This constant is integrable on s by hs.measure_ne_top, so continuousAt_of_dominated applies using the retained first-countability assumption. Empty s and zero measure cause no problem. This hypothesis can also be deleted together with first countability using the epsilon argument.
- `[SecondCountableTopologyEither Y E]` (theorem): Only the slice AEStronglyMeasurable step needs replacement. For each x, K = (f x) '' s is compact, hence closed and separable in E. After borelize E, continuity makes f x measurable. Its values lie in K almost everywhere for μ.restrict s: apply ae_restrict_iff to the measurable predicate f x y ∈ K. Then aestronglyMeasurable_iff_aemeasurable_separable supplies the required strong measurability. No measurability of s is needed. The remaining proof is unchanged; the criterion also handles empty K and zero restricted measure.

### [`CategoryTheory.NormalEpiCategory.mono_of_zero_kernel`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/NormalMono/Equalizers.lean#L299-L313) — `mathlib-0212`

Snippet: `samples/mathlib/mathlib-0212.lean`

- `[HasCokernels C]` (variable): Avoid constructing coequalizers. For u,v : T ⟶ X with u ≫ f = v ≫ f, put a = coprod.desc u v and q = coprod.desc (𝟙 T) (𝟙 T). The split epimorphism q is normal by normalEpiOfEpi, so it is a cokernel of some w with w ≫ q = 0. Coproduct identities give a ≫ f = q ≫ u ≫ f, hence (w ≫ a) ≫ f = 0. KernelFork.IsLimit.lift' applied to l implies w ≫ a = 0, since its kernel arrow is zero. CokernelCofork.IsColimit.desc' then gives d with q ≫ d = a. Precomposing with the two coproduct inclusions yields u = d = v. This uses no general cokernel existence and works unchanged for zero morphisms and trivial categories.

### [`DifferentiableOn.continuousMultilinear_apply_const`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean#L208-L211) — `mathlib-0251`

Snippet: `samples/mathlib/mathlib-0251.lean`

- `[Finite ι]` (variable): DifferentiableOn is defined for topological vector spaces, so its statement needs no finiteness. ContinuousMultilinearMap.apply 𝕜 M H u (Topology/Algebra/Module/Multilinear/Topology.lean) is a continuous linear evaluation map for arbitrary ι. For each x ∈ s, choose a derivative d from hc x hx and use evaluation composed with d as the derivative. Apply ContinuousLinearMap.isBigOTVS_comp and IsBigOTVS.trans_isLittleOTVS to the derivative remainder; linearity identifies the resulting remainder with that of y ↦ (c y) u. This proves the conclusion without finiteness, including infinite or empty ι, trivial spaces, and empty s.

### [`ProbabilityTheory.Kernel.withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Kernel/RadonNikodym.lean#L336-L367) — `mathlib-0258`

Snippet: `samples/mathlib/mathlib-0258.lean`

- `(hsm : MeasurableSet s)` (theorem): Let C = (mutuallySingularSetSlice κ η a)ᶜ, which is measurable by measurableSet_mutuallySingularSetSlice. The existing proof applied to every measurable t ∩ C shows that (withDensity η (rnDeriv κ η) a).restrict C = (κ a).restrict C, by measure extensionality and Measure.restrict_apply. Evaluate this equality on arbitrary s ⊆ C and use Measure.restrict_eq_self on both sides. Thus s need not be measurable; the argument also covers empty sets and zero kernels.

### [`add_tsub_add_le_tsub_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Sub/Defs.lean#L160-L162) — `mathlib-0260`

Snippet: `samples/mathlib/mathlib-0260.lean`

- `[AddLeftMono α]` (variable): Without this instance, apply tsub_le_iff_left and commute the right-hand side to reduce the goal to a + c ≤ (b + (a - b)) + c. By tsub_le_iff_right, this is equivalent to (a + c) - c ≤ b + (a - b), which follows from add_tsub_le_right.trans le_add_tsub. All three lemmas are proved earlier without AddLeftMono. This argument uses only the remaining axioms and also covers trivial types; empty types are vacuous.

### [`MeasureTheory.Measure.prod_smul_left`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Prod.lean#L877-L881) — `mathlib-0275`

Snippet: `samples/mathlib/mathlib-0275.lean`

- `[hν : SFinite ν]` (variable): Split on whether ν is s-finite. In the positive case, install that instance and use the original proof. Otherwise, Measure.prod (Prod.lean:172–173) defines both products as zero. Also c • 0 = 0: by Measure.smul_apply and the scalar-tower identity, its value on any set is (c • 1) * 0 = 0. Thus the equality holds without hν, including for zero measures and empty types.


## Tau Ceti (18 flagged)

### [`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/Basic.lean#L952-L963) — `tauceti-0001`

Snippet: `samples/tauceti/tauceti-0001.lean`

- `(hN : N ≠ 0)` (theorem): Split on N = 0; retain the existing proof for N ≠ 0. At zero, Nat.primeFactors_zero makes both products equal 1, so it suffices to show (Gamma0 0).index = 0. Write this index as I. For every prime p, Gamma0_le_Gamma0_of_dvd (by simp) gives Gamma0 0 ≤ Gamma0 p. Thus Subgroup.index_dvd_of_le and Gamma0_prime_index give p + 1 ∣ I. If I > 0, choose a prime p ≥ I using Nat.exists_infinite_primes; Nat.le_of_dvd then gives p + 1 ≤ I, a contradiction. Hence I = 0, and the zero-level equation holds too.

### [`RootPairing.coroot'_nonpos_of_mem_negRoots`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/Chamber.lean#L325-L331) — `tauceti-0007`

Snippet: `samples/tauceti/tauceti-0007.lean`

- `[P.IsReduced]` (variable): Recover this instance from the retained [P.flip.IsReduced]. Module.IsReflexive.of_isPerfPair applied to P.toLinearMap and P.flip.toLinearMap gives reflexivity of M and N; Module.IsReflexive.to_isTorsionFree supplies both torsion-freeness instances. RootPairing.instFlipIsReduced applied to P.flip then gives P.flip.flip.IsReduced, which is P.IsReduced by RootPairing.flip_flip. The original proof now applies unchanged. This recovery uses the other reducedness hypothesis and requires no nonempty index type; when ι is empty the theorem is vacuous.
- `[P.flip.IsReduced]` (variable): Recover this instance from the retained [P.IsReduced]. Module.IsReflexive.of_isPerfPair applied to P.toLinearMap and P.flip.toLinearMap, followed by Module.IsReflexive.to_isTorsionFree, supplies torsion-freeness of both modules. RootPairing.instFlipIsReduced then supplies P.flip.IsReduced under the remaining finiteness, characteristic-zero and domain assumptions. The original proof applies unchanged. This recovery uses the other reducedness hypothesis and works without nonemptiness assumptions, including empty ι.

### [`TauCeti.cohomologicalDimensionAt_eq_of_isOpen_of_ne_top`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/CohomologicalDimension/OpenSubgroup.lean#L108-L115) — `tauceti-0009`

Snippet: `samples/tauceti/tauceti-0009.lean`

- `[TotallyDisconnectedSpace G]` (variable): Openness supplies the continuous coset factorization needed for Shapiro without total disconnectedness: Subgroup.exists_continuous_rightCosetFactorization_of_isOpen requires only a topological group. Use it instead of exists_continuous_rightCosetFactorization in the proofs of coindMap_surjective and bijective_explicitShapiroMap1. Their remaining steps need no total disconnectedness. These open-subgroup versions give exact coinduction and degree-one Shapiro; the dimension-shifting proof in Shapiro/AllDegrees.lean then gives Shapiro in every degree without this instance. Consequently the proof of the closed-subgroup inequality can be repeated for this open U, and the trace/descent proof supplies the reverse inequality as before. Compactness, openness and hG remain available. The constructions work for trivial groups and all p, including 0 and 1; no additional nontriviality or primality assumption is needed.

### [`HeckeRing.GLn.posDetInt_le_commensurator`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/HeckeRing/GLn/Basic.lean#L712-L717) — `tauceti-0020`

Snippet: `samples/tauceti/tauceti-0020.lean`

- `[NeZero n]` (variable): Neither posDetInt nor SLnZ requires this instance. Split on n = 0. For n ≠ 0, install NeZero n and use the existing proof. For n = 0, every matrix indexed by Fin 0 is equal by extensionality, so Units.ext shows every g : GL (Fin 0) ℚ equals 1. Consequently g belongs to the commensurator's underlying submonoid by one_mem, regardless of its posDetInt membership.

### [`TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Data/Nat/Factorization/GcdSplit.lean#L56-L71) — `tauceti-0078`

Snippet: `samples/tauceti/tauceti-0078.lean`

- `(hp : p.Prime)` (theorem): Split on whether p is prime. In the prime case, use the existing proof. Otherwise, Nat.factorization_eq_zero_of_not_prime makes both exponents zero, and Nat.ordCompl_of_not_prime makes the complementary parts m and n. The conclusion reduces to gcd m n = gcd m n * 1. This also covers p = 0 and p = 1, since p ^ 0 = 1.

### [`TauCeti.RoughForm.inChartAt_mpullback`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Geometry/Manifold/DifferentialForm/Pullback/Chart.lean#L37-L53) — `tauceti-0108`

Snippet: `samples/tauceti/tauceti-0108.lean`

- `(hf : MDifferentiableAt I I' f ((extChartAt I α).symm z))` (theorem): Split on hf. When it holds, use the existing proof. Otherwise, put e = extChartAt I α and x = e.symm z. The composite f ∘ e.symm cannot be MDifferentiableWithinAt on range I at z: composing such differentiability with mdifferentiableAt_extChartAt at x would make (f ∘ e.symm) ∘ e differentiable at x. Here e x = z by hz, e takes values in range I (extChartAt_coe), and e.symm ∘ e is locally the identity on the chart source. Thus MDifferentiableAt.congr_of_eventuallyEq would imply hf, a contradiction. Consequently mfderiv_zero_of_not_mdifferentiableAt and mfderivWithin_zero_of_not_mdifferentiableWithinAt make both derivative maps in the claimed identity zero. Expanding inChartAt_apply and mpullback_apply then proves equality pointwise. This also covers k = 0: both sides evaluate ω on the same empty vector family, rather than necessarily being zero forms. Empty or trivial types introduce no exception.

### [`LipschitzWith.ae_finite_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Function/AreaFormula/Real.lean#L119-L126) — `tauceti-0115`

Snippet: `samples/tauceti/tauceti-0115.lean`

- `(hs : NullMeasurableSet s volume)` (theorem): Let t := toMeasurable volume s. Volume on finite-dimensional U is σ-finite, so Measure.restrict_toMeasurable_of_sfinite gives volume.restrict t = volume.restrict s. Thus hint also gives integrability on t. Apply ae_summable_fiber to the measurable set t with constant weight 1, and use the original summability argument to obtain almost-everywhere finite fibers over t. Since s ⊆ t by subset_toMeasurable, Set.Finite.subset gives finite fibers over s. This also covers empty sets, zero-dimensional spaces, and vanishing Jacobians; no positivity assumption is needed.

### [`TauCeti.exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Cohomology.lean#L195-L206) — `tauceti-0118`

Snippet: `samples/tauceti/tauceti-0118.lean`

- `[FiniteDimensional K L]` (variable): Recover it locally using `Module.Finite.right ℚ_[p] K L` from `[Module.Finite ℚ_[p] L]` and the scalar tower, then use the original proof. Neither the conclusion nor another binder requires this instance. The lemma applies without additional nonemptiness assumptions.
- `[CharZero L]` (variable): The algebra map ℚ_[p] →+* L is injective because its source is a field and L is nontrivial. Mathlib supplies `CharZero ℚ_[p]`, so `charZero_of_injective_algebraMap` recovers `CharZero L` locally, after which the original proof applies. The statement does not require this instance; trivial-field cases are excluded by `[Field L]`.
- `[CharZero K]` (variable): Similarly, the injective algebra map ℚ_[p] →+* K and `charZero_of_injective_algebraMap` recover `CharZero K` locally. Then the original proof applies unchanged. No remaining binder or conclusion depends on this instance, and `[Field K]` excludes the trivial case. Both characteristic-zero hypotheses can also be deleted together.

### [`TauCeti.ContCohomology.explicitFiniteQuotientSystem2_obj`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/FiniteQuotient/Explicit.lean#L396-L402) — `tauceti-0131`

Snippet: `samples/tauceti/tauceti-0131.lean`

- `[IsTopologicalAddGroup M]` (variable): It follows from the remaining [AddCommGroup M], [TopologicalSpace M], and [DiscreteTopology M]. Mathlib/Topology/Algebra/Group/ContinuousInv.lean provides this instance via the additive version of isTopologicalGroup_of_discreteTopology. Using `omit [IsTopologicalAddGroup M] in`, the statement still elaborates and the proof remains `by rfl`. The instance also applies to the trivial group; no additional nontriviality assumption is needed.

### [`Matrix.ProjectiveSpecialLinearGroup.isParabolic_inv_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup/FinTwo.lean#L103-L117) — `tauceti-0134`

Snippet: `samples/tauceti/tauceti-0134.lean`

- `[NoZeroDivisors R]` (variable): Unfold IsParabolic and invert its existential witness instead of using isParabolic_mk_iff. For every a : SL(2, R), parabolicity of a⁻¹ is equivalent to parabolicity of a using the existing hscalar calculation and simplification: SpecialLinearGroup.coe_inv and Matrix.adjugate_fin_two identify the inverse with the adjugate, which preserves scalarity and discriminant. These calculations require only CommRing R. QuotientGroup.mk_inv shows that the inverted witness represents g⁻¹; applying this construction twice proves the equivalence. This works with zero divisors and in characteristic two, and in the trivial ring both sides are false because every matrix is scalar.

### [`TauCeti.IsFiniteType.exists_chain_of_reachable`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/FiniteType/Diagram.lean#L154-L185) — `tauceti-0149`

Snippet: `samples/tauceti/tauceti-0149.lean`

- `(h : IsFiniteType A)` (theorem): Choose a shortest finite chain from u to v whose consecutive forward matrix entries are nonzero. Such a chain exists: Reachable supplies a walk, and getVert_zero, getVert_length, adj_getVert_succ, and diagramGraph_adj give the required endpoints and nonzero entries without h. Minimality implies injectivity, since any repeated vertex permits deleting the intervening segment. It also implies the final vanishing condition: a nonzero entry from position i to position j with i + 1 < j permits shortcutting that segment, contradicting minimality. Minimize over matrix chains, not diagram walks, so no symmetric vanishing assumption is needed. Extend the chosen finite chain to ℕ using u. If u = v, the length-zero chain works; empty B cannot supply u. Thus neither finiteness nor the other finite-type conditions are required.

### [`TauCeti.rightTrace_biprod`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/CategoryTheory/Monoidal/Pivotal/Biproduct.lean#L114-L125) — `tauceti-0163`

Snippet: `samples/tauceti/tauceti-0163.lean`

- `[MonoidalPreadditive C]` (variable): Let A = X ⊞ Y and F = tensorRight Aᘁ. Rigidity makes F a left adjoint via tensorRightAdjunction, so it preserves coproducts and zero morphisms (preservesZeroMorphisms_of_isLeftAdjoint). Thus preservesBinaryBiproduct_of_preservesBinaryCoproduct applies. Applying IsBilimit.binary_total to isBinaryBilimitOfPreserves gives F.map biprod.fst ≫ F.map biprod.inl + F.map biprod.snd ≫ F.map biprod.inr = 𝟙 (F.obj A). Insert this identity into rightTrace_def and distribute composition using Preadditive alone. Functoriality identifies the two summands as rightTrace (biprod.fst ≫ biprod.inl ≫ f) and its snd/inr counterpart; rightTrace_comm yields the conclusion. This bypasses rightTrace_add and needs no tensor additivity. The argument also covers zero objects and trivial hom groups.

### [`MeasureTheory.Measure.rnDeriv_mul_measure_singleton`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Measure/Decomposition/Lebesgue.lean#L46-L58) — `tauceti-0170`

Snippet: `samples/tauceti/tauceti-0170.lean`

- `[MeasurableSingletonClass α]` (variable): The singular-part argument does not use this instance. For the remaining step, put f = μ.rnDeriv ν, which is measurable by measurable_rnDeriv. Even without measurable singletons, ν.withDensity f {x} = f x * ν {x}: the lower bound follows from withDensity_apply_le and lintegral_singleton'. For the upper bound, take the measurable set T = toMeasurable ν {x} ∩ {y | f y = f x}. It contains {x}, and monotonicity together with measure_toMeasurable gives ν T = ν {x}. Monotonicity of withDensity, withDensity_apply on T, setLIntegral_congr_fun, and setLIntegral_const give the upper bound. Then the original decomposition argument finishes, since add_apply works for arbitrary sets. This argument also handles infinite masses and zero density, without cancellation or division; an empty α supplies no x.

### [`TauCeti.exists_coprimePart_indK0_of_trivial_eq_nsmul`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Permutation/PrimePower.lean#L131-L148) — `tauceti-0194`

Snippet: `samples/tauceti/tauceti-0194.lean`

- `[Fact p.Prime]` (variable): Split using CharP.char_is_prime_or_zero k p. In the prime case, install Fact p.Prime and use the existing proof. If p = 0, choose D = C. Since C is a finite group, Nat.card_pos gives Nat.card C > 0, so 0 does not divide its cardinality. Nat.factorization_zero_right makes the coefficient 0^0 = 1, and Subgroup.relIndex_self gives the required index. The induced-class equality then reduces to reflexivity. This also covers trivial C.

### [`TauCeti.IsGradedExtInternallyFinite.shiftSourceInverse`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Homology/EulerCharacteristic/ExtEuler/Graded/Shift.lean#L304-L308) — `tauceti-0229`

Snippet: `samples/tauceti/tauceti-0229.lean`

- `[e.functor.Additive]` (variable): An equivalence preserves limits and zero morphisms, and Abelian C supplies binary products. Thus Functor.additive_of_preserves_binary_products proves e.functor.Additive without this assumption. After omitting the binder, introduce that derived instance locally and use the original proof unchanged. Neither IsGradedExtInternallyFinite nor Functor.Linear requires this binder to elaborate. The argument also covers trivial categories; empty categories are excluded by the finite products supplied by Abelian C.

### [`TauCeti.cwEulerChar_preimage_of_card_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/Covering.lean#L75-L88) — `tauceti-0231`

Snippet: `samples/tauceti/tauceti-0231.lean`

- `(hfin : ∀ b, Finite ↥(p ⁻¹' {b}))` (variable): Replace the cell-counting step using cellPreimageEquiv. If d ≠ 0, hd and Nat.finite_of_card_ne_zero give finiteness of each centre fibre, so Nat.card_sigma gives the required count. If d = 0, every centre fibre is empty or infinite by Nat.card_eq_zero. Their sigma type is therefore empty or infinite, hence also has Nat.card zero. The existing finite-dimensional sum argument then applies without hfin, including when C is empty.
- `[RelCWComplex.Finite C]` (variable): Keeping hfin, hd identifies each centre fibre with Fin d via Finite.equivFinOfCardEq. Together with cellPreimageEquiv, this identifies the lifted n-cells with cell C n × Fin d. Nat.card_prod gives the required cell-count identity even when cell C n is infinite or empty, and when d = 0. Unfold cwEulerChar and use finsum_congr and mul_finsum over ℤ instead of truncating to a finite-dimensional sum; mul_finsum requires no finite-support assumption.

### [`TauCeti.schwarzChristoffelEdgeAngle_comp_strictMono`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/GlobalTurning.lean#L114-L125) — `tauceti-0238`

Snippet: `samples/tauceti/tauceti-0238.lean`

- `[LocallyFiniteOrder ι]` (variable): The conclusion does not use this instance: schwarzChristoffelEdgeAngle is defined using a Fintype sum and real comparisons. After omitting the hypothesis, insert `letI : LocallyFiniteOrder ι := Fintype.toLocallyFiniteOrder` and retain the existing proof. This constructor is defined in Mathlib/Order/Interval/Finset/Defs.lean and applies using the remaining Fintype and LinearOrder instances, including for empty and singleton types.

### [`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isCompact`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/PDE/Regularity/HolderContinuity.lean#L238-L258) — `tauceti-0281`

Snippet: `samples/tauceti/tauceti-0281.lean`

- `[Nonempty ι]` (theorem): Split into nonempty and empty cases for ι. The nonempty case uses the existing proof. If ι is empty, EuclideanSpace ℝ ι is subsingleton, so every K is subsingleton. Choose α = 1 and C = 0; Set.Subsingleton.holderOnWith proves the conclusion for any function, including preciseRepresentative regardless of its junk values. This also covers empty K.


## Lean Pool (61 flagged)

### [`ViscositySolns.exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Aleksandrov/JetCalculus/Strictification/StrictifiedObjective.lean#L337-L370) — `lean-pool-0000`

Snippet: `samples/lean-pool/lean-pool-0000.lean`

- `(hr : 0 <= r)` (theorem): Split on 0 ≤ r. In that case, the existing proof applies, including r = 0 and n = 0. Otherwise r < 0, so Metric.closedBall_eq_empty makes the closed ball empty. Choose lambda = 0: CoordinateSemiconvexOn is vacuous on the empty set, since its definition requires x to belong to that set.

### [`NavierStokes.ParticularWaveBounds.pressure_class`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ParticularWaveBounds.lean#L1371-L1389) — `lean-pool-0009`

Snippet: `samples/lean-pool/lean-pool-0009.lean`

- `(hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)` (theorem): The inverse-square jets need only the positive lower bound. Set q n x = ‖N n x‖². By PolynomialJets.norm_sq, q has polynomial jets, and hb with hlower gives q ≥ b² > 0 on the domain. Mathlib's iter_deriv_inv and norm_iteratedFDeriv_eq_norm_iteratedDeriv bound the kth derivative of inversion there by k! / (b²)^(k+1), independently of any upper bound. Applying norm_iteratedFDerivWithin_comp_le as in PolynomialJets.compact_comp therefore gives polynomial jets for q⁻¹ without hupper. Use polynomialJets_unweighted and then retain the numerator, multiplication, and band_smul arguments of the existing proof. Empty domains cause no difficulty; zero normals are excluded on the domain, and zero frequencies remain valid because division by zero and the corresponding inverse-carrier multiplier are both zero.

### [`CKN.Leray.integral_ae_eq_integral_jointRep`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegularisedJointRep.lean#L247-L298) — `lean-pool-0024`

Snippet: `samples/lean-pool/lean-pool-0024.lean`

- `[CompleteSpace E]` (variable): Completeness follows from the remaining finite-dimensional complex normed-space assumptions by `FiniteDimensional.complete ℂ E`. Omit this hypothesis and install that result locally; the original proof then works, including for the zero-dimensional space. The integral definition does not require this instance to elaborate.
- `[FiniteDimensional ℂ E]` (variable): Keep the proof through `hkey`. For F(x) = I(x) - H(x), local integrability follows from `hIint` and `hHint`. On every measurable finite-measure set, `hkey` and `integral_sub` show that every constant inner product of F has integral zero. `integral_eq_zero_of_forall_integral_inner_eq_zero` therefore gives vector integral zero. Apply `ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite` directly to F, replacing the finite-basis argument. These lemmas require no finite dimensionality or nontriviality and cover zero measures and trivial E.

### [`IsoGraph.Canon.splitCell_tr_general`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Equivariance.lean#L3331-L3342) — `lean-pool-0028`

Snippet: `samples/lean-pool/lean-pool-0028.lean`

- `(hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))` (theorem): The definition of splitCell shows that neither scatterFrom nor writeFrom affects the trace or the inputs to boundsFrom. Destructure their actual outputs and apply splitCell_eq_general using those equations, together with hb, h1, h2, ho and hbd; projecting .tr proves the conclusion without hsc or hw. This works for empty arrays and zero fuel as well. Both hypotheses can be deleted simultaneously.
- `(hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))` (theorem): Destructure the actual result of writeFrom and supply its equation instead of hw to splitCell_eq_general. Its lab and pos outputs disappear upon projecting .tr, leaving the desired equality. No nonemptiness or index-validity assumptions are needed, including for empty blocks. This hypothesis can also be deleted together with hsc.

### [`ESS.buCut_gradient_absorption`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUShortGradient.lean#L28-L102) — `lean-pool-0033`

Snippet: `samples/lean-pool/lean-pool-0033.lean`

- `(hκ : 0 ≤ buCutScalar κ z)` (theorem): Split on whether buCutScalar κ z is nonnegative. In the nonnegative case, use the supplied proof. Otherwise the left side is nonpositive, while the right side is nonnegative by hM and nonnegativity of square roots and vec3EuclideanNorm. Zero cutoff values and vanishing gradients are covered.
- `(hM : 0 ≤ M)` (theorem): The remaining hypothesis hderiv implies 0 ≤ |spatialPartial (buCutScalar κ) (0 : Fin 3) z| ≤ M. Derive hM from this and use the existing proof unchanged. Fin 3 has the index 0, so there is no empty-index exception; zero derivatives also give the required bound.

### [`IsoGraph.Canon.individualize_refines`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Progress.lean#L192-L202) — `lean-pool-0038`

Snippet: `samples/lean-pool/lean-pool-0038.lean`

- `(hv : v < n)` (theorem): Split on v < n; the existing proof handles that case. Otherwise, hp.posSize and getElem!_neg give p.pos[v]! = 0. If n = 0, Refines is vacuous. If n > 0, hp.cstLe gives p.cst[0]! = 0. By individualize_cst_eq and setCstFrom_getElemD (using hp.cenLe and hp.cstSize), individualization changes only cst entries at 1 ≤ k < p.cen[0]!, setting them to 1. No such k was an old cell start: hp.cellCst at position 0 gives p.cst[k]! = 0, contradicting p.cst[k]! = k and k ≥ 1. All old cell starts therefore remain unchanged, proving Refines without hv.

### [`TauCeti.DavisKahanExt.le_riccati_small_root_of_quadratic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Riccati/BoundedSharpEstimates.lean#L41-L89) — `lean-pool-0045`

Snippet: `samples/lean-pool/lean-pool-0045.lean`

- `(hb : 0 ≤ b)` (theorem): Split on 0 ≤ b; the original proof handles that case, including b = 0. If b < 0, multiplying hquad by -4*b and rearranging gives (d - 2*b*t)^2 ≤ D, where D = d^2 - 4*b^2. Hence D ≥ 0 and Real.le_sqrt_of_sq_le gives d - 2*b*t ≤ sqrt D. Set s = sqrt D and r = 2*b/(d+s). By hd and Real.sqrt_nonneg the denominator is positive; Real.sq_sqrt and field algebra give 2*b*r = d-s. Thus 2*b*r ≤ 2*b*t, and b < 0 implies t ≤ r. This also covers D = 0.
- `(hd : 0 < d)` (theorem): It follows from hb and hsmall: 0 ≤ 2*b < d. Recover hd with nlinarith and retain the original proof. This cannot be deleted together with hsmall: b = 1, d = 0, t = 1/2 satisfies the remaining hypotheses but makes the conclusion false.
- `(hsmall : 2 * b < d)` (theorem): Split on 2*b < d and use the original proof in that branch. Otherwise hd and d ≤ 2*b imply d^2 - 4*b^2 ≤ 0. Real.sqrt_eq_zero_of_nonpos reduces the right-hand side to 2*b/d, which is at least 1 by hd and d ≤ 2*b. Then ht1 proves the conclusion, including the zero-discriminant case. This cannot be deleted together with hd, as the counterexample given for hd shows.

### [`NavierStokes.HeatedOutgoing.E_times_U`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/HeatedOutgoing.lean#L1197-L1206) — `lean-pool-0047`

Snippet: `samples/lean-pool/lean-pool-0047.lean`

- `(hXR : 0 < XR)` (theorem): Keep hX and split on XR. For XR > 0, use the existing proof. If XR = 0, both radii vanish: division by zero, Real.log_zero and OutgoingSchedule.sigma_zero make the heat multiplier 1; TerminalCompensation.correction_support makes the correction at 0 vanish. If XR < 0, X / patchRadius F XR < 0, so correction_support again makes the patch increment zero. Put y = Real.log (X / XR) and s = HeatTailEdit.switchStart F.data. Real.log_div and Real.log_mul require only nonzero arguments and give log (X / switchRadius F XR) = y - s. If y ≤ s, sigma_zero makes the multiplier 1. Otherwise U vanishes by Profile.logU_after, since core.endpoint ≤ s, as established in the proof of pulseEnd_le_switch. Thus the heat contribution also preserves E*U.
- `(hX : 0 < X)` (theorem): Keep hXR and use the existing proof for X > 0. At X = 0, Real.log_zero and OutgoingSchedule.sigma_zero make the heat multiplier 1, while TerminalCompensation.correction_support forces the correction at 0 to vanish. For X < 0, the patch coordinate is negative, so correction_support makes the patch increment zero. Set y = Real.log (X / XR) and s = HeatTailEdit.switchStart F.data. The sign-independent Real.log_div and Real.log_mul give log (X / switchRadius F XR) = y - s. When y ≤ s, sigma_zero makes heatE equal OutgoingDilation.E. When y > s, Profile.logU_after makes U zero because core.endpoint ≤ s (the clock inequality established in pulseEnd_le_switch). These cases prove the same conclusion without hX.

### [`RS.tensorPow_id_ne_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/SuperEmbed/Standard.lean#L336-L359) — `lean-pool-0048`

Snippet: `samples/lean-pool/lean-pool-0048.lean`

- `[MonoidalPreadditive A]` (theorem): Let F := tensorRight U. Using tensorRightTensor, (tensoringRight A).mapIso hUU, and rightUnitorNatIso gives e : F ⋙ F ≅ 𝟭 A. Functor.IsEquivalence.mk' F e.symm e therefore makes F an equivalence, hence full. Functor.preservesZeroMorphisms_of_full then supplies F.map_zero without MonoidalPreadditive. Replace zero_whiskerRight in the given induction with this zero-preservation fact; everything else is unchanged. The k = 0 case still follows from hone, which also excludes a zero unit and trivial-category degeneracies. The statement itself needs only Preadditive for its zero morphism.

### [`OS4Ergodicity.OS4''_implies_OS4_Ergodicity`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OSforGFF/OS/OS4Ergodicity.lean#L1196-L1200) — `lean-pool-0073`

Snippet: `samples/lean-pool/lean-pool-0073.lean`

- `os4DoublePrimeClustering m → (unnamed hypothesis, introduced as h_cluster)` (theorem): QFT.gaussianFreeField_satisfies_OS4_PolynomialClustering in OS/OS4Clustering.lean proves clustering for every positive exponent using only m and [Fact (0 < m)]. Specializing to 6 gives os4DoublePrimeClustering m by its definition. Import that file and supply this proof to OS4''_implies_OS4', then OS4'_implies_OS4, instead of h_cluster. The retained positivity instance excludes zero and negative masses; the clustering result covers all test functions, including zero.

### [`EulerOrdinarySobolev.Evolution.gradient_logarithmic_envelope`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/OrdinaryEulerBKM.lean#L109-L141) — `lean-pool-0078`

Snippet: `samples/lean-pool/lean-pool-0078.lean`

- `(hC : 0 ≤ C)` (variable): Derive hC from hlog t and hW t. By tensorNorm_nonneg, Real.one_le_exp, and Real.log_nonneg, log (exp 1 + tensorNorm 3 (U.velocity t)) is nonnegative. Thus R := 1 + ‖(U.velocity t).toLp‖ + W t * log (exp 1 + tensorNorm 3 (U.velocity t)) satisfies R ≥ 1 > 0. The lemma U.gradientNormPath_nonneg t and hlog t give 0 ≤ C * R, so nonneg_of_mul_nonneg_left yields 0 ≤ C. The existing proof then works unchanged using this derived hC. This also covers T = 0 and zero velocity: the supplied t exists and R remains at least 1.

### [`MaxAddDegree.represents_zero_of_degree_lt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConwayRefinement/ConwayRefinement/Algebra/Valuation/DegreeRepresentatives.lean#L140-L143) — `lean-pool-0082`

Snippet: `samples/lean-pool/lean-pool-0082.lean`

- `[IsOrderedCancelAddMonoid M]` (variable): Represents, homogeneousMk, and the associated graded additive group do not require this instance. Replace the call to homogeneousMk_eq_zero_iff (which carries it) by unfolding homogeneousMk: componentMk_eq_zero_iff, explicitly declared with this instance omitted, sends h to componentMk m ⟨x, h.le⟩ = 0; applying DirectSum.of and its map_zero proves class_eq. The degree_le field is h.le as before. This argument also works for trivial rings and monoids and uses no cancellation or compatibility of addition with order.

### [`NavierStokes.SignedCopyBounds.local_mul`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SignedCopyBounds.lean#L91-L97) — `lean-pool-0090`

Snippet: `samples/lean-pool/lean-pool-0090.lean`

- `(hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)` (theorem): Both hw and hv can be removed simultaneously. For bounds witnesses A,p and B,q at order m, each majorant is nonnegative wherever estimates are required: use `(norm_nonneg _).trans (ha n i x hx hi 0 (Nat.zero_le m))`, and likewise for hb. Thus the pointwise Leibniz argument underlying LocalJets.bilinear needs neither weight-sign assumption. Using JetBounds.norm_iteratedFDeriv_mul_le_on on local smoothness neighborhoods gives product bound 2^m times these majorants; majorant_mul yields witnesses 2^m*A*B and p+q. Smoothness follows by multiplication. Zero witnesses or weights cause no problem, and empty native regions impose no estimates.
- `(hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x)` (theorem): The same argument removes hv, even simultaneously with hw: the order-zero bounds already force both majorants to be nonnegative at every relevant native point. JetBounds.norm_iteratedFDeriv_mul_le_on and the binomial sum estimate then give witnesses 2^m*A*B and p+q via majorant_mul, without assuming either weight nonnegative globally. This also handles zero majorants and vacuous native regions.

### [`RS.kernelSubobject_tensorHom_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/KernelPow.lean#L729-L761) — `lean-pool-0091`

Snippet: `samples/lean-pool/lean-pool-0091.lean`

- `[MonoidalPreadditive A]` (theorem): This follows from rigidity and abelianness. TensorExact.lean provides limit preservation for both tensoring functors without this assumption. Preservation of terminal objects gives preservation of zero morphisms, and Functor.additive_of_preserves_binary_products gives additivity. Their map_zero and map_add properties supply all four fields of MonoidalPreadditive. Install that instance locally and retain the original proof. This also covers zero objects and trivial categories.
- `[Epi p₁]` (theorem): Retain the supplied proof as a helper for an epi first factor. For arbitrary p₁, factor it as e ≫ m using factorThruImageSubobject and the image-subobject arrow; e is epi and m is mono. Rigidity makes m ▷ W₂ mono. Since p₁ ⊗ₘ p₂ = (e ⊗ₘ p₂) ≫ (m ▷ W₂), kernelSubobject_comp_mono identifies its kernel with that of e ⊗ₘ p₂. Apply the helper to e and p₂. The kernels of e and p₁ are canonically isomorphic over Z₁, so their right-whiskered kernel arrows have identical image subobjects, giving precisely the stated bound. This factorization argument also applies when p₁ is zero or its image is a zero object.

### [`Egrs75.ClearingP3.lowDigits_half_pred_pow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Egrs75/SubtractBranch.lean#L172-L181) — `lean-pool-0093`

Snippet: `samples/lean-pool/lean-pool-0093.lean`

- `(hp : 3 ≤ p)` (theorem): Split on 3 ≤ p. In that case, use the existing induction proof. Otherwise, Odd p forces p = 1. Then (p ^ m - 1) / 2 = 0 for every m, so RoundUp.lowDigits_zero proves the conclusion. Thus the only additional odd base is harmless.

### [`NFChoice.Compiler.NFCompactLeafFinalGate.axSiCompact`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NFWeakPartition/NFCompactLeafFinalGate.lean#L209-L255) — `lean-pool-0096`

Snippet: `samples/lean-pool/lean-pool-0096.lean`

- `(hxy : x ≠ y)` (theorem): Split on x = y; retain the original proof when unequal. When equal, choose an empty set E for the existential witness. Such E follows from literalAxNin, obtained using realizes_literal_axiom hNF .axNin: starting with A = v x, NAND(A,A) gives its complement C, NAND(A,C) gives a universal set U, and NAND(U,U) gives E with no members. Since hyz and hyw remain, both x and y evaluate to E after the universal updates. By Wff.Holds and Class.Holds, both class-membership atoms are false, proving the biconditional. If S is empty, validity is vacuous because Var = Nat admits no valuation into S.
- `(hzw : z ≠ w)` (theorem): Keep v' as in the proof, but define xs as [W, v' z, Y, v x] and obtain hiff from hY (v' z) W. Then hz is immediate, and hw, hy, and hx follow using the remaining inequalities. The same holds_literalSingletonPairMem and holds_literalPairMem steps finish the proof; neither lemma requires distinct variable names. When z = w, v' z = W, so this simply specializes the literal axiom to its diagonal case. Empty carriers introduce no issue, since validity is vacuous.

### [`NavierStokes.TerminalCompensation.physicalProfile_family_contDiffOn`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalCompensation.lean#L1082-L1099) — `lean-pool-0105`

Snippet: `samples/lean-pool/lean-pool-0105.lean`

- `(hR : 0 < R)` (theorem): Only the proof of hb needs changing. Split on R = 0. If R = 0, div_zero makes baseProfile lam (z.2 / R) constant, so contDiffOn_const proves hb regardless of the value of the real power at zero. Otherwise, div_ne_zero hz.2.ne' hR0 replaces (div_pos hz.2 hR).ne'; Real.contDiffAt_rpow_const_of_ne applies to negative inputs too. The proofs of ha', hr, and the final multiplication remain unchanged: division by a constant is smooth even when that constant is zero.

### [`NavierStokes.PolarCharts.chart_finiteJets_uniform`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalGraphBounds.lean#L336-L354) — `lean-pool-0108`

Snippet: `samples/lean-pool/lean-pool-0108.lean`

- `(ha : 0 < a)` (theorem): The charts are smooth for every real a. From the definition of positiveRadius, for ℓ < 0 its value is ≤ ℓ < 0: when x ≤ ℓ use Real.smoothTransition.nonneg; when ℓ ≤ x use Real.smoothTransition.zero_of_nonpos. Thus for a < 0 the denominator in extendedBase never vanishes, while its square-root argument is positive by positiveRadius_pos applied to a²/32. The existing smoothness proof therefore extends to a < 0. For a = 0, positiveRadius 0 x = 0, so extendedBase is constantly (0,0) and each chart is constant. Replace chart_contDiff ha with this all-a smoothness result; the compactness and finite-sum proof is unchanged. Negative b gives an empty ball and causes no exception.

### [`NavierStokes.SlowStressSupport.axial_stress_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SlowStressSupport.lean#L2093-L2133) — `lean-pool-0111`

Snippet: `samples/lean-pool/lean-pool-0111.lean`

- `(hn : 0 < n)` (theorem): Its only use is proving hprev_le. Replace that line with `have hprev_le : n - 1 ≤ n := Nat.sub_le n 1`; the remaining proof is unchanged. All invoked lemmas allow n = 0, where truncated subtraction gives n - 1 = 0.
- `(hB : 0 ≤ B)` (theorem): Only the radial-support step uses hB. Split on 0 ≤ B and retain the existing proof in that case. If B < 0, the independently established hout makes axialDensity vanish at every nonnegative radius. Thus its primitive from 0 to any positive R is zero, using intervalIntegral.integral_congr and integral_zero, so axialStress is zero there. At nonpositive radii it is zero by the definition of stress. Consequently radialSupport holds everywhere; the smoothness and derivative proofs remain unchanged.

### [`NumberField.Odlyzko.summable_integral_norm_idealSet_complexPlaceMellinGaussian`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/CompletedZeta/ConeGaussianInterchange.lean#L96-L112) — `lean-pool-0115`

Snippet: `samples/lean-pool/lean-pool-0115.lean`

- `[IsTotallyComplex K]` (variable): Summability still holds for arbitrary number fields, although the integral formula changes. Put σ = s.re, x = idealSetElement K J a, N = idealSetIntNorm K J a, and P = ∏ w, (w x)^2. The assumption-free lemmas norm_complexPlaceMellinGaussian and integral_totallyComplexGaussian_eq_prod give the norm integral as C·P^(-σ), with C independent of a. There is a constant c > 0 such that w x ≥ c for every a and w: fundamentalCone is defined using a bounded logarithmic fundamental domain (ZSpan.fundamentalDomain_isBounded), and logMap_apply bounds log(w x) − log(N)/[K:ℚ]. The omitted place is bounded using the weighted product formula. Here N ≥ 1 by idealSetIntNorm_ne_zero, so log(N) ≥ 0. Consequently, InfinitePlace.prod_eq_abs_norm gives P = N·∏(w real), w x ≥ N·c^(nrRealPlaces K). Thus the integrals are bounded by a constant times N^(-σ), whose series is summable by summable_idealSet_inverseNormPower; apply Summable.of_norm_bounded. All bases are positive by idealSetElement_ne_zero, so no zero/junk-power cases arise. Empty indexing sets are harmless, and the logarithmic argument also covers unit rank zero.

### [`CKN.Leray.mildShiftedStokesIntegral_continuous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierMildIntegral.lean#L216-L225) — `lean-pool-0117`

Snippet: `samples/lean-pool/lean-pool-0117.lean`

- `(hFC : ∀ t, ‖F t‖ ≤ C)` (theorem): Only local bounds are needed. At each t₀, continuity and IsCompact.exists_bound_of_continuousOn bound ‖F‖ on [t₀ - 1 - T, t₀ + 1]; enlarge this bound to M ≥ 0. For |t - t₀| < 1 and τ ∈ (0,T], this bounds ‖F (t - τ)‖. Repeat the existing dominated-convergence proof with M replacing C: intervalIntegral.continuousAt_of_dominated_interval requires domination only near t₀. The same integrable Abel kernel applies. At τ = 0 the integrand is zero, and T = 0 gives a zero integral.
- `(hC : 0 ≤ C)` (theorem): Recover it as (norm_nonneg (F 0)).trans (hFC 0), then use the existing proof. This also covers C = 0. Both hC and hFC can in fact be removed together using the local-bound argument.
- `(hT : 0 ≤ T)` (theorem): Split on 0 ≤ T and use the existing proof in that case. Otherwise T < 0, and every τ in the unordered interval between 0 and T satisfies τ ≤ 0. By definition mildShiftedStokesIntegrand is then zero for every evaluation time. intervalIntegral.integral_congr and intervalIntegral.integral_zero show the trajectory is constantly zero. The endpoint T = 0 also gives a zero integral.

### [`ESS.buGaussian_shifted_trace_strip_tendsto`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUGaussianAverageTools.lean#L334-L436) — `lean-pool-0118`

Snippet: `samples/lean-pool/lean-pool-0118.lean`

- `(hB : MeasurableSet B)` (theorem): The two uses of hB can be removed by replacing setIntegral_congr_ae with integral_congr_ae for the restricted measure. Both integrand equalities hold pointwise for every q, so the existing pointwise proofs work without any membership assumption. MeasurePreserving.setIntegral_image_emb and setIntegral_parabolic_to_product require no measurability of B. Thus the same integral identity and transfer of htrace hold for arbitrary B, including empty or nonmeasurable B, without integrability assumptions; the identity also holds at ε = 0.

### [`NavierStokes.PressureStream.reconstructed_divergence_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PressureStream.lean#L773-L791) — `lean-pool-0120`

Snippet: `samples/lean-pool/lean-pool-0120.lean`

- `(hab : a < b)` (theorem): Split on a < b; the displayed proof handles that case. Otherwise b ≤ a, and γd is identically zero: if γd z ≠ 0, hs gives z.1 ≤ b ≤ a, contradicting TransportPrimitive.radial_zero_of_le hγ.continuous hs. This includes a = b. Unfolding weightedSource, normalizeSource, physicalCompact and streamPotential then gives streamPotential = 0, since all integrals have zero integrands. Both stream fields and their divergence are consequently zero by fderiv_zero and zero_div, including at p.1 = 0. No nontriviality assumption on E is needed.

### [`CKN.Core.HeatPotential.heatPotential_series_representation_of_morrey`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Core/HeatPotential/SubordinatedEnd.lean#L24-L142) — `lean-pool-0121`

Snippet: `samples/lean-pool/lean-pool-0121.lean`

- `(hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)` (theorem): Apply heatPotential_kernel_integrable_on_split with center z := q, retaining radius r and all other assumptions. Its ball-membership hypothesis follows from Metric.mem_closedBall_self hr.le. By heatPotential_near_far_cover, its integration domain is univ, as is the original split domain centered at z. Transport the resulting integrability facts between these equal domains to obtain hInt, then leave the remaining proof unchanged. This works for every q, including points outside the original ball; hr still excludes zero and negative radii.

### [`PDL.localInterpolantStep_oneSidedR`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/Local.lean#L307-L366) — `lean-pool-0128`

Snippet: `samples/lean-pool/lean-pool-0128.lean`

- `(def_rule : rule = LocalRule.oneSidedR orule YS_def)` (theorem): The instance `localRuleSubsingleton` in LeanPool/PDL/Local/Rules.lean makes each `LocalRule X YS` a subsingleton. Thus this equality follows from `Subsingleton.elim _ _`, including when the result set is empty. Delete the binder and introduce the same equality locally with that proof; the existing proof then works unchanged. No other binder or the conclusion references `def_rule`.

### [`GerverSofa.PartC.Stage2.rhoC_nonneg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MovingSofa/GerverSofa/KernelOnly/Core/Bundle006.lean#L896-L906) — `lean-pool-0129`

Snippet: `samples/lean-pool/lean-pool-0129.lean`

- `(ht : t ∈ Set.Icc (0 : ℝ) T)` (theorem): The result holds for every real t. By Romik.phi_pos_of_mem_box params_mem, params.phi > 0. In phases 2 and 3, the failed first condition gives params.phi < t, hence 0 ≤ t; use this instead of ht.1 in rhoC_phase2_nonneg and rhoC_phase3_nonneg. Phase 4 already uses only its branch conditions. The remaining branches are the nonnegative constants 1/2 and 0, so values outside [0,T], including negative t and zero, are covered.

### [`AVenhance.Infra.Section5.Contracts.sds_gradMatrix_entry_periodic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/Contracts/TermCenteredAnalyticSmooth.lean#L49-L57) — `lean-pool-0130`

Snippet: `samples/lean-pool/lean-pool-0130.lean`

- `(hF : Differentiable ℝ F)` (theorem): Each gradMatrix entry is fderiv ℝ (fun y => F y j) x (basisVec i). For a = latticeShift k, he gives (fun y => F (y + a) j) = (fun y => F y j + a j). Mathlib's unconditional fderiv_comp_add_right and fderiv_add_const therefore equate the component derivatives at x + a and x; evaluate at basisVec i. These lemmas also cover nondifferentiable points, where fderiv is zero, so no differentiability hypothesis is needed.

### [`RS.LaurentTail.injG_apply_of_not_mem`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/LaurentTail/Comparison.lean#L1239-L1247) — `lean-pool-0131`

Snippet: `samples/lean-pool/lean-pool-0131.lean`

- `[T1Space X]` (variable): The remaining [T2Space X] supplies this instance via Mathlib's T2Space.t1Space (Topology/Separation/Hausdorff.lean). Since T1Space is Prop-valued, proof irrelevance preserves the statement's dependent uses of this instance. Add [T1Space X] to the omit command; the existing proof works unchanged. This implication also holds for empty or trivial X.

### [`polytopeRoundedSupportCurve_regular`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OperatorTheory/Operator/Crouzeix/SmoothSupportCurve.lean#L231-L242) — `lean-pool-0133`

Snippet: `samples/lean-pool/lean-pool-0133.lean`

- `(hu : u.Nonempty)` (theorem): Split on whether u is nonempty, using the existing proof in the nonempty case. If u = ∅, its partition sum is zero, so Real.log_zero makes polytopeSoftSupport identically zero and polytopeRoundedSupport identically rho. This constant support is smooth, and deriv_const' shows its curvature radius is rho > 0. Thus smoothSupportCurve_regular proves the conclusion in the empty case too.

### [`QuadraticCarleson.packetPoint_abs_sub_right_ge`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/CounterexampleGeometry.lean#L68-L86) — `lean-pool-0135`

Snippet: `samples/lean-pool/lean-pool-0135.lean`

- `(hN : 100 ≤ N)` (theorem): Both hN and hk can be deleted together. Put n = k.toNat. Int.self_le_toNat gives k ≤ n, including negative k. From hj and hτ.2, k + τ - j < 0. Thus the absolute value is j - k - τ ≥ j - n - 1/2, which equals the left side by Nat.cast_sub hj. This works for every N, including zero.
- `(hk : k ∈ paperBohrIndices N)` (theorem): The estimate holds for every integer k, independently of membership. Int.self_le_toNat gives k ≤ k.toNat; hj and τ < 1/2 then show the absolute value equals j - k - τ ≥ j - k.toNat - 1/2. Nat.cast_sub hj identifies this with the required bound. Negative k, where k.toNat = 0, also satisfy this argument. Both hk and hN can be deleted together.

### [`NavierStokes.PhysicalCoordinateBounds.xLift_homogeneous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalCoordinateBounds.lean#L421-L426) — `lean-pool-0136`

Snippet: `samples/lean-pool/lean-pool-0136.lean`

- `(_hy : y ∈ positiveTime)` (theorem): The existing proof works unchanged without _hy. Unfolding reduces the equality to (r * y.2.1) / (r * y.1) = y.2.1 / y.1 using Real.rpow_zero. Mathlib's mul_div_mul_left requires only r ≠ 0, supplied by hr.ne', with no restriction on y.1. In particular, when y.1 = 0 both quotients are zero.

### [`NavierStokes.ActivationCone.natural_reference_bounds`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ActivationCone.lean#L819-L863) — `lean-pool-0138`

Snippet: `samples/lean-pool/lean-pool-0138.lean`

- `(hδlim : 2 * δ < ReferencePath.rampLimit)` (theorem): Choose ε with 0 < ε, ε < δ and 2 * ε < rampLimit using ReferencePath.exists_small_length hδ. The existing proof at width ε gives bounds on [0, τ₀], with 0 < τ₀ ≤ ε. Transfer these bounds to width δ on τ := min τ₀ (ε / 2). Indeed, unfolding ReferencePath.continuation, dampedSlope and ProfileHistories.primitive shows that continuations at widths δ and ε agree whenever p.1 < ε: throughout the integration interval between 0 and p.1, both cutoffs equal 1 by ReferencePath.slopeCutoff_one, so intervalIntegral.integral_congr applies. This equality holds on an open half-space, so Filter.EventuallyEq.fderiv_eq also identifies their radialPartial values. The definitions of referenceP1 and referenceP2 therefore give identical A and B on [0, τ], transferring every bound unchanged. This works for every positive δ, however large; τ is positive and ≤ δ, and positivity of A transfers as well, so no zero-denominator exception arises.

### [`NavierStokes.TerminalStress.swirlCoefficient_contDiffAt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalStress.lean#L412-L420) — `lean-pool-0158`

Snippet: `samples/lean-pool/lean-pool-0158.lean`

- `(hh1 : h < 1 / 2)` (theorem): Split on h < 1 / 2. The original proof handles that case. Otherwise 2 * h ≥ 1, so SimilarityCoordinates.coordinateQ is identically 1 by its definition, including at h = 1 / 2. Thus SimilarityProfile.X h p = p.2.1 and flattening h f p = f (Real.log p.2.1). Its required smoothness follows from hf by composition with contDiffAt_snd.fst.log, using hs to exclude zero. The physicalHeat smoothness proof uses only hh, ht and hs; the square-root division is unchanged.

### [`NavierStokes.TemporalMeanUpdate.meanClass_axialAlias`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TemporalMeanUpdate.lean#L1535-L1567) — `lean-pool-0159`

Snippet: `samples/lean-pool/lean-pool-0159.lean`

- `(hab : a < b)` (theorem): Split on a < b and use the existing proof in that case. Otherwise logStripData.domain = Prod.fst ⁻¹' Ioo a b is empty, including when a = b. By the definitions of MeanClass and MemClass, smoothness and bounds are then vacuous; choose C = 0 and p = 0.
- `(hh : 0 ≤ h)` (theorem): Only the chart-prefactor bound needs modification. The upper half of ChartScales.native_power_bounds uses Nat.lt_floor_add_one, which holds for every real nativeArgument, including negative arguments; it does not need hh. Consequently chartPrefactor h n ≤ ChartScales.Tg * ChartScales.S n for n ≥ 4 holds for arbitrary h. Absorb the four initial bands exactly as in chartPrefactor_bandBound_all, then reproduce meanClass_desiredIncrement and the remaining proof without hh.
- `(hM : ∀ n, M n ≠ 0)` (theorem): Replace the Fourier estimate in dividedAlias_global_bounds with TransportPrimitive.iteratedFDeriv_totalIntegral_norm_le, which bounds each integral jet by the source-jet bound times the support length for every M, including zero. Apply the fixed cutoff multiplier estimate, as in exactAlias_sourceJet_bound, then dividedAlias_finiteJets_transfer. The resulting constants are uniform in M. The existing interior-support argument proves meanClass_dividedAlias without hM, and the rest of this proof is unchanged.

### [`Malliavin.norm_sub_expectationL2_le_mderivD12`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/ClarkOcone.lean#L1095-L1102) — `lean-pool-0164`

Snippet: `samples/lean-pool/lean-pool-0164.lean`

- `(C : ClarkOconeFamily B P 𝓕)` (theorem): This is the Gaussian Poincaré inequality, independent of a Clark–Ocone family. The definitions identify mderiv with the Cameron–Martin gradient and D12 with its graph-closure domain. A replacement proof uses Gaussian interpolation: for independent X,Y with law P and mean m, put Y_t = m + t(X-m) + √(1-t²)(Y-m). Gaussian integration by parts gives Var(f(X)) = ∫₀¹ E⟨Df(X),Df(Y_t)⟩ dt for smooth bounded f. This calculation can be established first in finite-dimensional Gaussian coordinates and then by approximation; the library provides Gaussian integration by parts as integral_inner_mderiv. Since Y_t also has law P, Cauchy–Schwarz bounds the integral by E‖Df(X)‖². Finally, inGraphClosure_mderivClosure supplies smooth bounded approximants converging to F and its derivative; continuity of expectation and norms passes the inequality to F. No inverse covariance is used, so singular Gaussian laws are covered; for a Dirac law the centered norm is zero. IsGaussian already makes P a probability measure, excluding the zero-measure case.

### [`PDL.LoadedCluster.satDown_three_not_basic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/ClusterSatDown.lean#L575-L602) — `lean-pool-0171`

Snippet: `samples/lean-pool/lean-pool-0171.lean`

- `(hΔ : Δ ∈ C.lambdaTwo)` (theorem): This follows from hx and the construction of C.Q. Prove by QuasiTab.build.induct that every type-three subtree of build inC step Hist Γ has its label in inC: build_of_leaf has no such subtree; build_of_node creates its type-three node only under Γ ∈ inC, and recursive subtrees satisfy the induction hypothesis. Apply this invariant using QuasiTab.mem_subtrees_of_atOpt hx and the definition of LoadedCluster.Q, then retain the original proof. The invariant also covers type-three nodes with no children.
- `(hb : ¬ Δ.basic)` (theorem): Split on Δ.basic. The non-basic case uses the existing proof. In the basic case, hS.basicStep supplies Y with C.stepOf Δ = {Y}, hence C.stepOfL Δ = [Y] by the definitions of stepOfL and Finset.pdlSeqSort. Then hlen gives next.length = 1, hlab gives the child's label Y, and IH supplies SatDown for that child. Apply the preceding lemma satDown_three_basic. The length equality excludes an empty next in this branch.
- `(hlen : next.length = (C.stepOfL Δ).length)` (theorem): The proof only needs i < next.length for the index supplied by nonBasicStep. This follows from hlab i hi and hx: if next.length ≤ i, List.getElem?_eq_none, QuasiTab.atOpt_append, and the definitions of atOpt and labelAt make C.Q.labelAt (x ++ [i]) equal none, contradicting hlab i hi. Replace the omega step with this argument; everything else is unchanged. If the step list is empty, nonBasicStep already contradicts the satisfiability antecedent.
- `(hlab : ∀ i, (hi : i < (C.stepOfL Δ).length) → C.Q.labelAt (x ++ [i]) = some ((C.stepOfL Δ)[i]'hi))` (theorem): Recover hlab from hx by a construction invariant: every type-three subtree q of build inC step Hist Γ satisfies q.children.map QuasiTab.label = step q.label. Prove this by QuasiTab.build.induct using build_of_node, build_of_leaf, and QuasiTab.build_label; the newly created children are precisely builds of the step labels. Apply it to hx using QuasiTab.mem_subtrees_of_atOpt and LoadedCluster.Q. For each hi, hlen supplies the corresponding next index, and QuasiTab.atOpt_child plus labelAt gives hlab. Empty step lists require no indices. The original proof then applies.

### [`NavierStokesAndEuler.SmoothCutoff.cutoff_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/ForMathlib/SmoothCutoff.lean#L86-L90) — `lean-pool-0181`

Snippet: `samples/lean-pool/lean-pool-0181.lean`

- `(hR : 0 < R)` (theorem): Split on 0 < R. The positive case uses the existing proof. Otherwise R ≤ 0, so hx gives ‖x‖ ≤ 0, hence x = 0 by norm_le_zero_iff. Then smul_zero and baseCutoff_eq_one prove cutoff E R x = 1. This covers R = 0; negative R is incompatible with hx and norm_nonneg.

### [`BooleanIsoperimetry.harper_macaulay_min`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L154-L176) — `lean-pool-0191`

Snippet: `samples/lean-pool/lean-pool-0191.lean`

- `(ha : a ≤ 2 ^ N)` (theorem): Split on a ≤ 2^N, retaining the existing proof in that case. Otherwise set C = 2^N. The lemmas H_full and H_mono give C ≤ H N a. Thus the RHS is at least C + a ≥ 2*C, whereas H_le_cube bounds the LHS by 2^(N+1) = 2*C. This works also for N = 0 and b = 0. Both ha and hb can be deleted together by handling either oversized argument this way.
- `(hb : b ≤ 2 ^ N)` (theorem): Split on b ≤ 2^N, retaining the existing proof in that case. Otherwise set C = 2^N. By H_full and H_mono, C ≤ H N b. The RHS is therefore at least b + C ≥ 2*C, while H_le_cube bounds the LHS by 2^(N+1) = 2*C. This includes N = 0 and a = 0. Both bounds can also be deleted together.

### [`PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PebblingLean/UpperBoundParameters.lean#L2099-L2138) — `lean-pool-0205`

Snippet: `samples/lean-pool/lean-pool-0205.lean`

- `(hsmall : splitM K n < n)` (theorem): This follows from hslack alone. At n = 0, loss 0 = 0 contradicts hslack. At n = 1, the definition gives splitM K 1 = 0, since Real.log 1 = 0. For n ≥ 2, if n ≤ splitM K n, truncated subtraction gives splitA K n = 0, so hslack implies 1 ≤ loss n. But loss_le_of_le (with m = 2) gives loss n ≤ loss 2 = 1/4, a contradiction. Derive hsmall by these cases and then use the existing proof unchanged.

### [`LeanPool.Besicovitch.exists_nonnegative_score_of_matched_endpoint_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Besicovitch/SixPoint/EndpointFailureClosed.lean#L27-L46) — `lean-pool-0208`

Snippet: `samples/lean-pool/lean-pool-0208.lean`

- `(hweighted : weightedPairScore configuration.rootDisplacement barC lambda mu (configuration.redDisplacement .left) (configuration.redDisplacement .right) (configuration.bluePullback .left) (configuration.bluePullback .right) ≤ 0)` (theorem): Run the displayed proof instead at gramLambda = 1/12 and gramMu = 13/14, using gramLambda_pos and gramMu_pos. Admissibility supplies all premises of weightedPairScore_le_of_separated, which supplies the required weighted bound independently of hweighted. Its Gram-certificate proof does not depend on this endpoint theorem and can be placed earlier to avoid an import cycle. This works for every admissible configuration, including boundary cases.
- `(hlambda : 0 < lambda)` (theorem): Use the same endpoint argument at the fixed positive weights gramLambda and gramMu, obtaining its weighted bound from weightedPairScore_le_of_separated and h. Neither the original lambda nor its sign is used. Thus lambda may also be zero or negative.
- `(hmu : 0 < mu)` (theorem): Use the endpoint argument at gramLambda and gramMu, whose positivity is proved by gramLambda_pos and gramMu_pos; weightedPairScore_le_of_separated supplies its bound from h. The original mu is irrelevant, including when zero or negative.
- `(hred : redSiblingTriangleFailure configuration (.endpoint 0))` (theorem): Apply exists_nonnegative_score_or_matched_sibling_endpoint configuration h hmatching. Either it supplies the desired packing, or it supplies both endpoint failures at code 0 or 3. Close these branches using the fixed-Gram-weight endpoint argument described above, swapping both child pairs for code 3. Thus no pre-existing hred is required.
- `(hblue : blueSiblingTriangleFailure configuration (.endpoint 0))` (theorem): The lemma exists_nonnegative_score_or_matched_sibling_endpoint supplies either a packing or both required failures at a matched endpoint. The latter cases close using the fixed positive Gram weights and their geometric bound, with simultaneous child swapping for endpoint 3. The supplied hblue is therefore unnecessary.
- `(hmatching : SelectedDiagonalMatchingFails configuration)` (theorem): Admissibility alone suffices: exists_nonnegative_score_or_matching_obstruction gives a packing or a diagonal/anti-diagonal obstruction. For each obstruction, use the matched-sibling-endpoint alternative and the fixed-Gram-weight closure above; swapBlueChildren handles the anti-diagonal branch, and unswapBlue preserves the score. This reconstructs the finite-property proof without circularly invoking this theorem. Indeed, all six reported hypotheses can be deleted together while retaining h.

### [`NavierStokes.PhysicalParticularWave.bandPressureMode_eq_physical`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalParticularWave.lean#L1179-L1206) — `lean-pool-0212`

Snippet: `samples/lean-pool/lean-pool-0212.lean`

- `(hKr : referenceFrequency D j ≠ 0)` (theorem): Split on whether the reference frequency is zero. The nonzero case uses the existing proof. In the zero case, reference pressure vanishes because copyPressure divides by that frequency. Also normalWeight is zero, so transportTangent has zero normal. Thus its pressureCoefficient, whose denominator is the normal's squared norm, is zero by division by zero. Consequently all transported copy pressures and their periodized sum vanish. Both modes are therefore zero.
- `(hz : 0 < z.2 0)` (theorem): The graph identity used twice in the proof holds for arbitrary radius. Its only positivity-dependent step is commonGraph_radialScale. For a > 0 and arbitrary r and b, (a*r)^b = a^b*r^b: for r ≥ 0 use Real.mul_rpow; for r < 0 use Real.rpow_def_of_neg, Real.rpow_def_of_pos, Real.log_mul and exp_add. This also covers r = 0, including b = 0. Apply this with a = Q^(-1/2) to extend commonGraph_radialScale, then commonGraph_map and cylinderChange_graph without radius positivity. The remaining proof is unchanged.

### [`AleksandrovDifferentiability.prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/AleksandrovDifferentiability/Analysis/GoodSet.lean#L97-L106) — `lean-pool-0218`

Snippet: `samples/lean-pool/lean-pool-0218.lean`

- `(hs : MeasurableSet s)` (theorem): Use hbad.exists_measurable_subset_ae_eq to obtain measurable t ⊆ s \ G with the same product measure. For each x, its section T is measurable by measurable_prodMk_left, lies inside the section S of s, and is disjoint from G. Thus hsection and ae_iff give (ν.restrict S) T = 0 by measure_mono. Measure.restrict_apply identifies this with ν T because T ⊆ S, without requiring S measurable. Measure.measure_prod_null then gives product measure zero for t, and measure_congr transfers this to s \ G. This works also for empty sections and zero measures.
- `[SFinite ν]` (theorem): Split on whether ν is s-finite. In the positive case, install that instance and use the original proof. Otherwise Measure.prod is zero by its definition, which explicitly uses zero when the second measure is not s-finite, so the conclusion is immediate. Alternatively, replace the use of measure_prod_null in the underlying proof by Measure.measure_prod_null_of_ae_null, which requires no s-finiteness.

### [`Zeta5Irrational.cov_302_304`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta5Irrational/Table/Intervals.lean#L7296-L7302) — `lean-pool-0219`

Snippet: `samples/lean-pool/lean-pool-0219.lean`

- `0 < t (named h0 in the proof)` (theorem): The lower bound h1 already implies positivity: establish 0 < (723732917263 / 2560000000000 : ℝ) by norm_num, then use lt_of_lt_of_le with h1 to recover h0. The existing proof then works unchanged. Zero and negative t are excluded by h1 alone.

### [`TauCeti.DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_reducingSubspace`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/SinTheta/Natural/Reducing.lean#L496-L543) — `lean-pool-0223`

Snippet: `samples/lean-pool/lean-pool-0223.lean`

- `(hAdense : Dense (A.domain : Set ER))` (theorem): Replace its use in the problem record by hA.dense_domain, using Mathlib's IsSelfAdjoint.dense_domain. This includes trivial spaces and rules out nondense domains even with the adjoint's junk-value convention.
- `(hAclosed : A.IsClosed)` (theorem): Replace its use in the problem record by hA.isClosed, using Mathlib's IsSelfAdjoint.isClosed. This holds for every self-adjoint partial map, including on trivial spaces.
- `(hA0dense : Dense (A0.domain : Set FR))` (theorem): Replace its use in the problem record by hA0.dense_domain, using Mathlib's IsSelfAdjoint.dense_domain. The lemma covers trivial spaces and the adjoint's junk-value convention.
- `(hA0closed : A0.IsClosed)` (theorem): Replace its use in the problem record by hA0.isClosed, using Mathlib's IsSelfAdjoint.isClosed. This holds without nontriviality assumptions. All four reported hypotheses can also be deleted together.

### [`BGS.CorvajaZannier.exists_support_direction_of_not_rankTwo`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveSupportRank.lean#L186-L216) — `lean-pool-0224`

Snippet: `samples/lean-pool/lean-pool-0224.lean`

- `(hnonsingleton : ∃ s ∈ f.support, s ≠ r)` (theorem): Split on whether such an s exists. If so, use the existing proof. Otherwise every s ∈ f.support equals r, so planeExponentDifference r s is zero by its definition. Choose the nonzero vector v := fun _ => (1 : ℤ) and take k = 0 for every support element. This covers singleton support; empty support is excluded by the retained hr.

### [`ViscositySolns.SmoothConvexApproximationOnInteriorClosedBallTheorem.of_extensionMollification`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Jensen/ConvexMollification.lean#L285-L308) — `lean-pool-0232`

Snippet: `samples/lean-pool/lean-pool-0232.lean`

- `(hmoll : ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem n)` (theorem): MainTheorems.lean:42–86 independently proves ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem.proof without assumptions beyond n, and without using the theorem under review. Move or inline that mollifier construction to supply hmoll internally, then retain the existing argument. This covers every n, including zero; the required positive radius margin follows from r < R already present in the definitions.

### [`CarlsonFunctions.SeveralComplexVariables.norm_sub_le_of_separately_analytic_bounded`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CarlsonFunctions/SeveralComplexVariables/LocallyBounded.lean#L67-L108) — `lean-pool-0237`

Snippet: `samples/lean-pool/lean-pool-0237.lean`

- `(hr : 0 < r)` (theorem): Split on 0 < r, using the existing proof in the positive case. Otherwise, Metric.nonneg_of_mem_closedBall hx gives 0 ≤ r, hence r = 0. By Metric.closedBall_zero, hx and hy give x = c and y = c, so both sides simplify to zero. Negative radii are excluded by hx. This also handles empty ι and trivial F.

### [`EulerPacketTerminalDatum.forwardInitializedPacket_normalized_bound`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/PacketForwardInitializedCorrectionData.lean#L76-L84) — `lean-pool-0242`

Snippet: `samples/lean-pool/lean-pool-0242.lean`

- `(hα : 0 < α)` (variable): Evaluate hgrowth at t = ⟨0, le_rfl, D.T_pos.le⟩. Since L.initial_one gives L.g t = 1, timeProfileChange_pos applied to S.growth_pos yields 0 < α. The interval is nonempty because D.T_pos holds. Recover hα this way and use the existing proof unchanged.
- `(hN : 1 ≤ N)` (theorem): Split into N = 0 and 1 ≤ N. In the latter case use the existing proof. For N = 0, sourcePacketPullbackField_path is a sum over Finset.range 0, hence zero, and scaling preserves its zero path. Apply Field.wordBound_zero, WordBound.of_path_eq, and WordBound.mono_amplitude. The required amplitude is nonnegative by BC.multiplierCost_nonneg and fixedVelocityGradeCost_nonneg, using L.radius_one. Thus the excluded zero case also satisfies the conclusion.

### [`LeanPool.Besicovitch.sigma_mul_radius_div_two_le_diam_localAttachmentComponent`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Besicovitch/Rectifiability/ComponentDiameter.lean#L38-L191) — `lean-pool-0244`

Snippet: `samples/lean-pool/lean-pool-0244.lean`

- `(hsigma : 0 ≤ sigma)` (theorem): Split on 0 ≤ sigma. In that case use the existing proof. Otherwise, hrho implies sigma * rho / 2 ≤ 0, so Metric.diam_nonneg proves the conclusion directly, including for empty or zero-diameter components.
- `(hsigma_one : sigma < 1)` (theorem): Its only use is to establish hR_rho. Instead, extract w from hannulus. Metric.mem_ball and nonmembership in the inner ball give sigma * rho / 2 ≤ dist w z < rho. This supplies hR_rho without any upper bound on sigma; the remaining proof is unchanged.
- `(hchosen : chosen ⊆ badConvexSets mu F alpha)` (theorem): It is used only for compactness of Q. The proof of isCompact_compactAttachmentUnion generalizes to arbitrary chosen under hF and hsum. Keep its finite-large-attachments argument. For each small V, its finite ediam gives boundedness by Metric.isBounded_iff_ediam_ne_top, and ediam_convexAttachment_le gives attachment diameter < epsilon. If F ∩ diameterThickening 2 V is empty, the attachment is empty by convexHull_empty and closure_empty. Otherwise choose f in that intersection: f belongs to F and the attachment, so every attachment point is within epsilon of F. This replaces the uses of badness and positive diameter in the compactness proof. All subsequent steps remain unchanged.
- `(hrho : 0 < rho)` (theorem): Extract w from hannulus. Its outer-ball membership gives 0 < rho by Metric.pos_of_mem_ball. Reconstruct hrho this way and retain the existing proof. Thus hannulus already excludes zero and negative rho.

### [`EulerTransversePacketProvider.Forcing.velocityPath_reflection_neg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/TransversePacketParity.lean#L374-L380) — `lean-pool-0247`

Snippet: `samples/lean-pool/lean-pool-0247.lean`

- `(hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)` (variable): Embed the supported forcing and initial datum into Supported P _ Set.univ measurableSet_univ. These embeddings intertwine coefficient multiplication by supportedOperatorMap_coe and supportedOperator_eq_square. EulerLinearDuhamel.Evolution.solution_map therefore identifies the embedded coordinate solution with the solution on univ; physicalVelocity commutes with these embeddings too. Apply EulerSourceCylinderParity.velocity_reflection_neg on univ, whose symmetry is automatic, and transfer its full-cylinder equality back. No compactness of univ is required by these results. This argument also covers empty support and zero data.
- `(hM : ∀ t x, D.M.field t (-x) = D.M.field t x)` (variable): Replace D.frameDerivative_even hF hM in the proof by evenness obtained through differentiation. D.frame_even hF makes the clamped frame paths at -x and x identical. D.frame_derivative supplies their within-interval derivatives, so UniqueDiffWithinAt.eq_deriv identifies the frameDerivative values. The required uniqueness follows from uniqueDiffOn_Icc D.T_pos, including both endpoints. Thus the existing proof works without hM; the zero-length interval degeneracy is excluded by D.T_pos.

### [`Zeta5Irrational.tc_361`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta5Irrational/Table/Intervals.lean#L2671-L2676) — `lean-pool-0249`

Snippet: `samples/lean-pool/lean-pool-0249.lean`

- `0 < t` (theorem): The lower bound already implies positivity: `norm_num` proves `(0 : ℝ) < 46687825988961 / 128000000000000`, and `linarith` with the retained lower-bound hypothesis gives `0 < t`. Supply this derived fact to the existing `check_right` application. Thus zero and negative t remain excluded without this hypothesis.

### [`CKN.norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Poincare/Lp.lean#L159-L202) — `lean-pool-0254`

Snippet: `samples/lean-pool/lean-pool-0254.lean`

- `[MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]` (theorem): By ENNReal.toReal_pos_iff, hvol implies volume U < ∞. Since volumeMeasureOn U abbreviates volume.restrict U, MeasureTheory.isFiniteMeasure_restrict supplies this instance locally, after which the original proof applies unchanged. Zero and infinite volume are already excluded by hvol.
- `(hu : MeasureTheory.IntegrableOn u U)` (theorem): Let G be the segment integral in hsegment. The existing segment estimate gives ‖u x - u y‖ ≤ G y everywhere. ContDiff.continuous and Continuous.aestronglyMeasurable make y ↦ u x - u y ae strongly measurable. Thus MeasureTheory.Integrable.mono' applied to hsegment proves this difference integrable on U. The constant u x is integrable by the finite-measure instance, so Integrable.sub' recovers integrability of u; then the original proof applies. This also works for d = 0, and hvol excludes null or empty U.

### [`Bananas.TwiceMarkedBananas.s5_lem5_3_1`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BrillNoetherGraphs/TwiceMarkedBananas.lean#L2116-L2135) — `lean-pool-0261`

Snippet: `samples/lean-pool/lean-pool-0261.lean`

- `(hconn : graphConnected M.graph)` (theorem): Connectivity follows from hTau. Otherwise choose a nonempty cut S with no crossing edges and M.u ∉ S. From the definitions of firingVector and principalDivisors, linear equivalence preserves the coefficient sum over S. Put C = max 0 (∑ x ∈ S, D x). Every twist D + a•oneChip M.u - b•oneChip M.v with b ≥ 0 has rank at most C: subtracting (C+1) chips at a vertex of S leaves negative S-degree, hence an unwinnable divisor. This uses rank_geq_iff; rank_geq_neg_one supplies the lower bound −1. These library bounds transfer through rank_toLib.

Write r(a,b) for the twist's rank. Choose N > 2(C+1), and integers A ≤ B containing tau b for every 0 ≤ b < N. Summing hTau's rankDelta equation over A ≤ a ≤ B and 0 ≤ b < N gives N. But telescoping gives r(B,0) − r(A−1,0) − r(B,N) + r(A−1,N), which is at most 2(C+1), a contradiction. Thus disconnected graphs cannot satisfy hTau, including unwinnable cases where ranks equal −1. Singleton graphs are already connected, and CFGraph excludes empty vertex types. Derive connectivity this way and then apply the existing proof.

### [`EGZ.CommonMeasure.final_mass_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ErdosGinzburgZiv/EGZ/Decomposition/CommonMeasure.lean#L109-L119) — `lean-pool-0276`

Snippet: `samples/lean-pool/lean-pool-0276.lean`

- `(hε : 0 < ε)` (theorem): Split on 0 < ε. The positive case uses the existing proof. Otherwise ε / 2 ≤ 0, while mass_nonneg u hu gives nonnegative masses for P and Q. Thus ε / 2 * mass u P ≤ 0 ≤ mass u Q. This includes ε = 0 and empty types.
- `(hR : 0 < R)` (theorem): Split on 0 < R, using the existing proof in the positive case. Otherwise mass_weight_mono w u hle P and hP give mass u P ≤ R ≤ 0. Together with mass_nonneg u hu P this forces mass u P = 0, so the conclusion follows from mass_nonneg u hu Q. This covers R = 0 and empty types; R < 0 is incompatible with these inequalities.

### [`NavierStokes.ActualCycleCoherence.source_fiber_continuous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ActualCycleCoherence.lean#L714-L723) — `lean-pool-0279`

Snippet: `samples/lean-pool/lean-pool-0279.lean`

- `(hS : ∀ l n, IsClosed (S l n))` (theorem): Split on 0 < p.1. In the positive case, compose source_positive_smooth H with the fiber inclusion; this lemma requires neither hS nor hpos. Otherwise the fiber source is identically zero: H.inputSupport and hpos make every nonzero real-projected input coefficient vanish throughout the domain where the radius is nonpositive. This property is preserved by the literal residual operations. In particular, a function vanishing on that half-space has zero total Fréchet derivative there, including at radius zero: any existing derivative vanishes by one-sided directional limits; a nonexistent derivative totalizes to zero (fderiv_zero_of_not_differentiableAt). HarmonicFields.derivativeCoefficient therefore preserves this vanishing, as do convolution, angular differentiation and real projection. The residual's zero mode is zero by ParticularWaveAssembly.residualSource_zero. Thus the nonpositive-radius fiber is constant zero, without any closedness assumption on S.

### [`eigenvector_constant_sign`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SpectralPositivity/Operator/JentzschProof.lean#L332-L387) — `lean-pool-0280`

Snippet: `samples/lean-pool/lean-pool-0280.lean`

- `(hT_compact : IsCompactOperator T)` (theorem): Its only use is passing it to abs_eigenvector_of_top_eigenvector. That lemma's proof never uses its corresponding parameter _hT_compact. Inlining that proof without the parameter leaves the remaining proof unchanged, including all degenerate cases.
- `(hT_sa : IsSelfAdjoint T)` (theorem): A direct argument avoids self-adjointness. Set a = |f|, u = a + f and v = a - f, both nonnegative. The eigenvector equation, norm_abs_eq_norm and hlam₀_top give ⟨a,Ta⟩ ≤ ⟨f,Tf⟩. Expanding shows ⟨u,Tv⟩ + ⟨v,Tu⟩ ≤ 0. Both terms are nonnegative by positivity preservation, so ⟨u,Tv⟩ = 0. If v = 0, f is nonnegative. Otherwise Tv is strictly positive almost everywhere; L2.inner_def, L2.integrable_inner and integral_eq_zero_iff_of_nonneg_ae imply u = 0 almost everywhere, hence u = 0 by Lp.eq_zero_iff_ae_eq_zero. Thus -f is nonnegative. Apply ground_state_strictly_positive to f or -f respectively. Zero measure is excluded by hf_ne; neither this argument nor the final positivity step needs self-adjointness.
- `(hlam₀ : 0 < lam₀)` (theorem): Positivity follows from the other assumptions. Let a = |f|, which is nonnegative and nonzero by norm_abs_eq_norm and hf_ne. Positivity improvement gives Ta > 0 almost everywhere. Consequently ⟨a,Ta⟩ > 0: it is nonnegative, and equality would imply a·Ta = 0 almost everywhere using L2.inner_def, L2.integrable_inner and integral_eq_zero_iff_of_nonneg_ae, forcing a = 0 by Lp.eq_zero_iff_ae_eq_zero. Now hlam₀_top gives 0 < ⟨a,Ta⟩ ≤ lam₀ * ‖a‖², forcing lam₀ > 0. Supply this derived fact to the original proof. This also handles degeneracy: zero measure would contradict hf_ne.

### [`QuadraticCarleson.annularQuadraticKernel_correlation_le_ordered`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/QuadraticFixedHeightAveragingCorrelation.lean#L49-L127) — `lean-pool-0281`

Snippet: `samples/lean-pool/lean-pool-0281.lean`

- `(hR : 0 < R)` (theorem): Split on 0 < R and use the existing proof in that case. R = 0 contradicts hH and hlam. If R < 0, Icc (R / 4) R is empty, so hasupp forces a = 0 and the integral vanishes. The majorant is nonnegative: unfold quadraticFixedHeightMajorant and use S > 0, u > 0 and D² ≥ 0.
- `(hS : 0 < S)` (theorem): Recover it from hR and hRS: 0 < R ≤ S. The existing proof then applies unchanged; S = 0 and negative S are excluded by the remaining hypotheses.
- `(hH : 0 < H)` (theorem): Since hu gives u^5 > 0, hdecay implies H > 0: otherwise H * u^5 ≤ 0, contradicting 1 ≤ H * u^5. Recover hH and retain the existing proof.
- `(hD : 0 ≤ D)` (theorem): The inequalities 0 ≤ ‖a 0‖ ≤ D / R imply D / R ≥ 0. Since hR makes R positive, D ≥ 0 follows. Recover hD before the existing proof; D = 0 is allowed.
- `(hu : 0 < u)` (theorem): From hH and hdecay, u^5 must be positive. An odd fifth power is nonpositive when u ≤ 0, so u > 0 follows. Recover hu and use the existing proof.
- `(hu1 : u ≤ 1)` (theorem): For u ≤ 1 use the existing proof. For u > 1, norm_phase and the amplitude bounds bound the integrand's norm by D²/(R*S); it vanishes outside [x-R,x]. Restricting to that interval and applying intervalIntegral.norm_integral_le_of_norm_le_const gives a bound D²/S. If |x-y| > 2*S, the support assumptions and hRS instead force the integrand identically zero. Otherwise the majorant is (2*D²/S) times either 1 or 8403968*u, both at least 1. This also covers D = 0.
- `(hab : ∀ t, ‖a t‖ ≤ D / R)` (theorem): Recover hab from ha, hab' and hasupp. Because R > 0, hasupp gives a 0 = 0. The Mathlib lemma norm_image_sub_le_of_norm_deriv_le_segment', applied on [0,R], gives ‖a t‖ ≤ (D/R²)*t ≤ D/R there. Outside the support a t = 0, and every support point lies in [0,R]. Thus hab follows, including when D = 0, and the existing proof applies.
- `(hbb : ∀ t, ‖b t‖ ≤ D / S)` (theorem): Recover hbb from hb, hbb' and hbsupp. Since S > 0, b 0 = 0. Applying norm_image_sub_le_of_norm_deriv_le_segment' on [0,S] yields ‖b t‖ ≤ (D/S²)*t ≤ D/S there. Every support point lies in this interval, and elsewhere b vanishes. This includes D = 0 and supplies hbb for the existing proof.

### [`AVenhance.Infra.Section3.ChiMKCorrector.chiMK_spaceLap_three_active`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section3/ChiMKCorrector.lean#L159-L209) — `lean-pool-0282`

Snippet: `samples/lean-pool/lean-pool-0282.lean`

- `(hk : k % 4 = 3)` (theorem): Split on k % 4 = 3. In that case, use the existing proof. Otherwise, the definition of uShear makes its component 0 identically zero: the k % 4 = 1 branch has first component zero, and the remaining branch is the zero vector. Thus Ingredients.chiMK also has component 0 identically zero. Apply the preceding lemma ChiMKCorrector.chiMK_spaceLap_of_zero_component. This proves the unchanged conclusion for every k; the additional cases reduce to 0 = 0 without any division assumptions.

### [`TauCeti.sum_sq_principalCosines_eq_sum_sq_norm_projection`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean#L747-L767) — `lean-pool-0283`

Snippet: `samples/lean-pool/lean-pool-0283.lean`

- `[U.HasOrthogonalProjection]` (theorem): FiniteDimensional 𝕜 E implies FiniteDimensional 𝕜 U. Mathlib's RCLike.properSpace_submodule instance supplies ProperSpace U, complete_of_proper supplies CompleteSpace U, and Submodule.HasOrthogonalProjection.ofCompleteSpace recovers this hypothesis automatically. The statement still elaborates and the existing proof works unchanged. This includes U = ⊥ and zero-dimensional E. Both projection hypotheses can also be deleted together.
- `[V.HasOrthogonalProjection]` (theorem): FiniteDimensional 𝕜 E implies FiniteDimensional 𝕜 V. Mathlib's RCLike.properSpace_submodule instance supplies ProperSpace V, complete_of_proper supplies CompleteSpace V, and Submodule.HasOrthogonalProjection.ofCompleteSpace recovers this hypothesis automatically. The statement still elaborates and the existing proof works unchanged, including V = ⊥ and zero-dimensional E. Both projection hypotheses can also be deleted together.

### [`Malliavin.memLp_mderiv_cylinder_expGrowth`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/CylindricalGrowth.lean#L488-L496) — `lean-pool-0295`

Snippet: `samples/lean-pool/lean-pool-0295.lean`

- `(hC : 0 ≤ C)` (theorem): Evaluate hfg' at y = 0. Since ‖0‖ = 0 and Real.exp_zero = 1, it gives ‖fderiv ℝ f 0‖ ≤ C. Norm nonnegativity implies 0 ≤ C, recovering hC for the existing proof. This also works when n = 0.
- `(hc : 0 ≤ c)` (theorem): Split on 0 ≤ c. The existing proof handles that case. Otherwise c < 0, so c * ‖y‖ ≤ 0; Real.exp_le_exp and Real.exp_zero give C * Real.exp (c * ‖y‖) ≤ C using hC. Apply memLp_mderiv_cylinder_of_dominated with the original derivative bound and constant dominating function ψ = C. Its square is integrable by integrable_expGrowth_sq μ C 0 0 after simplification. This includes C = 0, n = 0, and trivial W.

### [`Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_of_generated`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/BrownianPurePowerDuality.lean#L393-L402) — `lean-pool-0298`

Snippet: `samples/lean-pool/lean-pool-0298.lean`

- `(hsm : ∀ t, StronglyMeasurable (B t))` (theorem): Derive it from generated instead: `have hsm : ∀ t, StronglyMeasurable (B t) := fun t => (generated.measurable t).stronglyMeasurable`. The library's `IsWienerGenerated.measurable` gives coordinate measurability, and Mathlib's `Measurable.stronglyMeasurable` applies because the target is ℝ. Then use the original proof unchanged. This derivation requires no nonemptiness or nondegeneracy assumptions and also covers trivial spaces.


## FLT (Anthropic) (79 flagged)

### [`P2MW.S_ModularCurve_full_eq_adjoin_primes.ModularCurve.W1.roots_prime_at_slot_roots_nodup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_full_eq_adjoin_primes.lean#L306-L312) — `flt-anthropic-0001`

Snippet: `samples/flt-anthropic/flt-anthropic-0001.lean`

- `(hζ : IsPrimitiveRoot (ζ : K) N)` (theorem): Pass to L = AlgebraicClosure K. Since K is a ℚ-algebra and p is prime, L has a primitive p-th root, by AlgebraicClosure.hasEnoughRootsOfUnity and HasEnoughRootsOfUnity.exists_isPrimitiveRoot; it is a unit. Apply the preceding roots_prime_at_slot and roots_prime_at_slot_nodup over L with N := p and divisibility dvd_rfl. The injective coefficient map F : LaurentSeries K →+* LaurentSeries L carries the polynomial in the conclusion to this polynomial over L: use coeffMap_qExpand, and check compatibility with qTwist and coeffEmb coefficientwise from their definitions. Descend nodup using Polynomial.map_roots_le_of_injective, Multiset.nodup_of_le, and Multiset.Nodup.of_map. This does not use hζ, N, or ζ, and works even when the original polynomial has no roots in K.
- `(hpN : p ∣ N)` (theorem): The conclusion is independent of N. Use the algebraic-closure argument described for hζ: choose a primitive p-th root there and apply the two preceding lemmas with N := p and dvd_rfl, then descend along the injective coefficient map using Polynomial.map_roots_le_of_injective and the multiset nodup lemmas. No divisibility assumption on the original N is needed, including when N = 1.
- `[NeZero N]` (theorem): Neither IsPrimitiveRoot (ζ : K) N nor p ∣ N requires this instance to elaborate. Prove the conclusion after extending coefficients to AlgebraicClosure K, choosing a primitive p-th root and using the preceding two lemmas with N := p; descend nodup via Polynomial.map_roots_le_of_injective, Multiset.nodup_of_le, and Multiset.Nodup.of_map. Thus the proof is independent of the original N, including N = 0. This hypothesis, hζ, and hpN can all be omitted together.

### [`P2MW.S_ModularCurve_FullLevel_mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin.P3aW_node14.chartAlgFin_eq_of_mem_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin.lean#L96-L99) — `flt-anthropic-0008`

Snippet: `samples/flt-anthropic/flt-anthropic-0008.lean`

- `[Fact (a ≠ 0)]` (theorem): chartAlgFin R F a is defined as the elements integral over Algebra.adjoin R {a}, without a nonzero requirement. Reprove chartAlgFin_le_of_mem using its displayed proof, which uses neither nonzero fact, then apply it in both directions. Integrality transitivity works unchanged when a = 0. Both nonzero hypotheses can be deleted together.
- `[Fact (b ≠ 0)]` (theorem): The displayed proof of chartAlgFin_le_of_mem uses neither nonzero fact: it transports integrality along the adjoin inclusion and applies isIntegral_trans. Using this argument in both directions proves equality even when b = 0, since chartAlgFin has no nonzero requirement. Both nonzero hypotheses can be deleted together.

### [`P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.C2idemCore.IdempotentOrbit.exists_idempotent_orbit_or_isField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.lean#L172-L278) — `flt-anthropic-0014`

Snippet: `samples/flt-anthropic/flt-anthropic-0014.lean`

- `[Finite ι]` (theorem): The other assumptions imply finiteness. If ι is empty, it is already finite. Otherwise choose j₀ and put t = conj φ s. Since n > 0 and t^[n] = id, t is a ring automorphism. In an arbitrary product of fields, the primitive nonzero idempotents are exactly the singleton indicators: coordinatewise, IsIdempotentElem.iff_eq_zero_or_one makes every idempotent a characteristic function, and any larger support contains a proper singleton idempotent. Automorphisms preserve this characterization. Thus each e_m = t^[m](ind {j₀}) is a singleton indicator. Set q = 1 - ∏ m ∈ Finset.range n, (1 - e_m). Coordinatewise q is idempotent; cycling the factors shows t q = q. The proof's hfix01 argument uses no finiteness, so q is 0 or 1. Its j₀-coordinate is 1, hence q = 1. Consequently the supports of these n singleton indicators cover ι, proving Finite ι. Install this derived instance and use the existing proof unchanged.

### [`P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6.comp_heckeDiag_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.lean#L664-L678) — `flt-anthropic-0018`

Snippet: `samples/flt-anthropic/flt-anthropic-0018.lean`

- `(hp : p ≠ 0)` (theorem): Split on p = 0. In the zero case, ModularForm.heckeDiagMatrix_zero gives heckeDiagMatrix 0 = 1, so the identity action reduces the conclusion to hF (proved by `simpa using hF`). In the nonzero case, use the existing proof with the nonzero hypothesis supplied by the case split.

### [`P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.AlgebraicGeometry.RelPicard.ChartHypotheses.exists_cover_chart_of_cover`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.lean#L154-L166) — `flt-anthropic-0028`

Snippet: `samples/flt-anthropic/flt-anthropic-0028.lean`

- `(hDU : D.SupportedIn U)` (theorem): The ideal-module base-change isomorphism follows from D.flat, without support or invertibility assumptions. Affine-locally over T, write the ambient ring as A over B and D as A/J. D.flat makes A/J flat over B. Applying LinearMap.lTensor_injective_of_exact_of_flat to 0 → J → A → A/J → 0 shows that J ⊗[B] k identifies with the extended ideal in A ⊗[B] k. These canonical identifications glue to the isomorphism eI used in nonempty_chartModule_iso, replacing its two support-dependent invertibility arguments. The sectionTwist isomorphism and the remaining cover-transport proof are unchanged. This argument also covers zero rings, empty charts, zero or unit ideals, and e = 0 or r = 0.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.CHRAux.Tr_fixed`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.lean#L97-L99) — `flt-anthropic-0032`

Snippet: `samples/flt-anthropic/flt-anthropic-0032.lean`

- `[DecidableEq G]` (variable): Tr is a Fintype sum and does not require decidable equality. The existing proof works unchanged after `omit [DecidableEq G] in`: neither Equiv.mulLeft nor Fintype.sum_equiv requires it. Reindexing by left multiplication works for every finite group, including the trivial group, and for the zero ring.

### [`P2MW.S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator.D628.coe_bar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator.lean#L382-L384) — `flt-anthropic-0034`

Snippet: `samples/flt-anthropic/flt-anthropic-0034.lean`

- `[NeZero p]` (variable): Neither modularFunctionFieldFull nor bar requires NeZero p: the former adjoins divisorExpansions p, and the latter pairs coeffEmb with coeffEmb_mem_laurentBaseChange. These definitions remain valid at p = 0. Using `omit [NeZero p] in`, the identical statement is still proved by `rfl`.

### [`P2MW.S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.Blk176Arith.not_cube_dvd_mul_prod_filter`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.lean#L147-L182) — `flt-anthropic-0038`

Snippet: `samples/flt-anthropic/flt-anthropic-0038.lean`

- `(hN0 : N ≠ 0)` (theorem): The remaining hypotheses imply N ≠ 0: add `have hN0 : N ≠ 0 := by intro h; exact hN3 q hq (h ▸ Nat.dvd_zero (q ^ 3))`. Here Nat.dvd_zero confirms that N = 0 contradicts hN3. The existing proof then works unchanged, including when S is empty.

### [`P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.WeierstrassCurve.Affine.isPrincipal_of_geomDivisorSum_eq_zero'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean#L2026-L2070) — `flt-anthropic-0040`

Snippet: `samples/flt-anthropic/flt-anthropic-0040.lean`

- `[HasPrincipalDivisors F W.FunctionField]` (theorem): This follows from the retained [W.IsElliptic] by WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic, found in Theorems/Thm_WeierstrassCurve_hasPrincipalDivisors_functionField_of_isElliptic.lean. Affine and toAffine are abbreviations, so its result is the required instance. Import that theorem and install its result with letI; the existing proof then applies unchanged. The lemma holds in every characteristic without additional assumptions, and Field already excludes empty or trivial fields.

### [`P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.P2mS17LB.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.lean#L49-L111) — `flt-anthropic-0046`

Snippet: `samples/flt-anthropic/flt-anthropic-0046.lean`

- `(hn : 0 < n)` (theorem): The remaining hypothesis hqn implies n ≠ 0: if n = 0, then q divides n, contradicting hqn. Thus recover 0 < n and use the original proof.
- `(hqn : ¬ (q : ℕ) ∣ n)` (theorem): Take a finite normal extension E containing F₀, ζ and α, and let r be the cardinality of Gal(E/ℚ). This is positive, including when the group is trivial. Restrict primeLocalToGlobal q φ using AlgEquiv.restrictNormalHom; pow_card_eq_one shows its r-th power is identity. Apply exists_level_dvd_of_frobenius_pow_mem_inertia_sup with base E and positive modulus n*d*r, then take the normal closure F. By H_anti, membership of φ^m in H q F forces n*d*r ∣ m. Consequently n*d ∣ m and the restriction of primeLocalToGlobal q (φ^m) to E is identity, so it fixes α by AlgEquiv.restrictNormalHom_apply. This works even when q divides n.
- `(hζ : IsPrimitiveRoot ζ n)` (theorem): No root-of-unity property is needed. Choose a finite normal E containing F₀ and the arbitrary elements ζ, α. Let r > 0 be the cardinality of Gal(E/ℚ). Using exists_level_dvd_of_frobenius_pow_mem_inertia_sup with modulus n*d*r and then normal closure gives F for which membership forces n*d*r ∣ m, by H_anti. The restricted automorphism has r-th power identity by pow_card_eq_one, so it fixes α at every such m. This also handles ζ = 0 and trivial Galois groups.
- `(hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ))` (theorem): The same finite-group construction works for arbitrary α: choose finite normal E containing F₀, ζ and α, and put r = card Gal(E/ℚ) > 0. Apply exists_level_dvd_of_frobenius_pow_mem_inertia_sup with modulus n*d*r and take normal closure. H_anti yields n*d*r ∣ m; pow_card_eq_one applied to the restricted automorphism then shows primeLocalToGlobal q (φ^m) fixes α. No division by α is used, so α = 0 is included. This hypothesis, hζ and hqn can be deleted together if hn is retained.

### [`P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.PLCDSol.exists_gamma0_apply_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.lean#L883-L889) — `flt-anthropic-0048`

Snippet: `samples/flt-anthropic/flt-anthropic-0048.lean`

- `[NeZero M]` (variable): Split on M = 0. When M ≠ 0, install the local NeZero instance and use the existing proof. When M = 0, ZMod 0 is definitionally ℤ, so Int.units_eq_one_or gives d = 1 or d = -1. Choose γ = 1 or γ = -1 respectively. Both matrices have determinant 1 and lower-left entry zero, hence belong to Gamma0 0 by CongruenceSubgroup.Gamma0_mem; their upper-left entries are the required values. The statement itself requires no NeZero instance.

### [`P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.CohCarrier.gammaH_inf_gamma0_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.lean#L104-L128) — `flt-anthropic-0049`

Snippet: `samples/flt-anthropic/flt-anthropic-0049.lean`

- `[NeZero N]` (theorem): The existing proof needs no nonzero assumptions: GammaH, gamma0Units, mem_GammaH_iff, Gamma0Map, and ZMod.unitsMap are defined for every modulus. The castHom argument also works for every modulus. Both NeZero binders can be deleted together; ZMod 0 is ℤ and ZMod 1 is a valid trivial ring, so these cases cause no exception.
- `[NeZero (N * ℓ)]` (theorem): The existing proof works unchanged without this binder, even when ℓ = 0: ZMod 0 is ℤ, and castHom and unitsMap still provide reduction to ZMod N. Gamma0 membership and the lower-right unit commute with this reduction exactly as in the proof. Both NeZero binders can be deleted together.

### [`TateCurve.pointX_inv_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_TateCurve_XMultStructure.lean#L171-L175) — `flt-anthropic-0057`

Snippet: `samples/flt-anthropic/flt-anthropic-0057.lean`

- `(hq0 : q ≠ 0)` (theorem): In fact pointX q t⁻¹ = pointX q t holds for every q and t. From the definition xfun w = w / (1 - w)^2, inversion invariance holds also at w = 0 and w = 1 by simplification; otherwise use xfun_inv. Thus zpow_neg and inversion of products give xTerm q t⁻¹ (-n) = xTerm q t n even when q = 0. Unfold pointX and apply tsum_comp_neg and tsum_congr, as in the source proof of pointX_inv. Apply this identity to t = u * v⁻¹.
- `(hu0 : u ≠ 0)` (theorem): Split on u = 0. In that case inv_zero and zero_mul make both arguments of pointX equal to zero, so the conclusion is reflexive. Otherwise the existing proof applies.
- `(hv0 : v ≠ 0)` (theorem): Split on v = 0. In that case inv_zero and mul_zero make both arguments of pointX equal to zero, so the conclusion is reflexive. Otherwise the existing proof applies.
- `(hdiv : OffLattice q (u * v⁻¹))` (theorem): The only use of this condition in the source proof of pointX_inv is to apply xfun_inv away from 1. But xfun 1⁻¹ = xfun 1 is reflexive, and both values are zero under division-by-zero conventions. Extend xfun_inv to this case, then repeat the termwise identity and tsum_comp_neg/tsum_congr proof without the OffLattice condition.
- `[CompleteSpace K]` (variable): The definitions of pointX, s₁, and coeffSum do not use completeness. Repeat the source proof of pointX_inv directly: establish its termwise inversion identity using the remaining nonzero and OffLattice assumptions, then use tsum_comp_neg and tsum_congr. Neither lemma requires completeness or summability, so nonsummable series cause no exception.
- `[IsUltrametricDist K]` (variable): The definitions in the conclusion do not use ultrametricity. Replace the call to pointX_inv with its source proof, proving the rational identity xfun w⁻¹ = xfun w directly by clearing denominators and field algebra under the remaining nonzero and OffLattice assumptions. Finish with tsum_comp_neg and tsum_congr, which require no ultrametric assumption and also cover nonsummable series.

### [`P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.Nat.not_mem_placesOf_of_mem_placesOf_of_coprime`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.lean#L72-L74) — `flt-anthropic-0058`

Snippet: `samples/flt-anthropic/flt-anthropic-0058.lean`

- `(hℓ : ℓ ≠ 0)` (theorem): The definition of placesOf gives placesOf 0 = ∅, using Ideal.span_singleton_zero. Split on ℓ = 0: the zero case contradicts hv; otherwise use the existing disjoint_placesOf_of_coprime proof with the recovered nonzero hypothesis. Both nonzero hypotheses can also be deleted together.
- `(hℓ' : ℓ' ≠ 0)` (theorem): Split on ℓ' = 0. In the zero case, placesOf 0 = ∅ by its definition and Ideal.span_singleton_zero, so the conclusion holds immediately. Otherwise apply the existing disjoint_placesOf_of_coprime proof with the recovered nonzero hypothesis. Both nonzero hypotheses can also be deleted together.

### [`P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.lean#L843-L876) — `flt-anthropic-0059`

Snippet: `samples/flt-anthropic/flt-anthropic-0059.lean`

- `(hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))` (theorem): This follows from hprime and hres. Write d for the completion degree. Its positivity gives finite-dimensionality by Module.finite_of_finrank_pos. IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, and Module.finrank_mul_finrank show that orderOf θ divides d. Since d is prime, this order is either 1 or d. But hres excludes θ = 1, hence excludes order 1. Reconstruct hθ and use the existing proof. Primality excludes zero-degree and degree-one cases.
- `(hn : ‖n‖ = 1)` (theorem): Split on m = 0. For m > 0, one_lt_q and hm give ‖1 - n‖ < 1, so the ultrametric inequality implies hn and the existing proof applies. For m = 0, hm gives ‖n‖ ≤ 1. If hn holds, again use the existing proof. Otherwise n has valuation < 1. Under hw, θ preserves valuation: decompose each nonzero element using exists_eq_algebraMap_mul_unit, then apply v_algebraMap and v_theta_eq_one. Applying valuation to hc consequently gives v(c)^d = v(n) < 1, hence v(c) < 1 since hprime.pos gives d > 0. Thus θ y - c*y has the same valuation as y, using Valuation.map_sub_eq_of_lt_left for y ≠ 0; y = 0 is immediate. Its integer-subgroup comap is therefore exactly the integer subgroup. The other comap contains that subgroup because hϖ makes ϖ integral. The intersection is the integer subgroup itself, so AddSubgroup.relIndex_self gives 1, matching the right side for m = 0. This also covers n = 0 and c = 0.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L610-L612) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- `[CharZero L]` (variable): The same proof works after omitting this instance. In Definitions/Def_ModularCurve_LaurentCoeff.lean, algebraMap_laurentSeries_eq_single requires only [Field L]; HahnSeries.C_apply unfolds C c to single 0 c without a characteristic assumption. Thus both sides equal single 0 c over any field, including positive characteristic and c = 0.

### [`P2MW.S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_qExpansionDiffAlong_traceDiff_pullbackDiff_heckeBetaC_self.lean#L856-L872) — `flt-anthropic-0062`

Snippet: `samples/flt-anthropic/flt-anthropic-0062.lean`

- `(hτ₂ : τ ⟨jqNModC K p, jqNModC_mem K p⟩ = ⟨jqModC K, jqModC_mem K p⟩)` (theorem): It follows from hτ₁. Write F = modularFunctionFieldC K p, j = jF K p and j' = jpF K p, using LevelHeckeDiff's definitions. Since A0 = K(j), hτ₁ identifies τ on A0 with phi0; this follows by IntermediateField.adjoin_algHom_ext. Applying τ to the minimal-polynomial relation for j' therefore shows PF.IsRoot (τ j'). The definition of QF and PF_isRoot_jF give PF = (X - C j) * QF. But minpoly_yR and isIntegral_yR show QF is irreducible, while QF_map and natDegree_Qexp give its degree p > 1. Thus Irreducible.not_isRoot_of_natDegree_ne_one excludes a root in F, forcing τ j' = j. Supply this derived equality to the existing proof. There are no exceptional zero cases: primality gives p ≥ 2, and hζ gives (p : K) ≠ 0. The two swapping hypotheses can each be deleted separately, but not both.
- `(hτ₁ : τ ⟨jqModC K, jqModC_mem K p⟩ = ⟨jqNModC K p, jqNModC_mem K p⟩)` (theorem): Retaining hτ₂ gives τ.symm j = j'. Apply the implication proved in the preceding justification to τ.symm: any such automorphism sending j to j' must send j' to j. Hence τ.symm j' = j, equivalently τ j = j', recovering hτ₁ for the existing proof. The same prime and primitive-root assumptions exclude the degenerate cases. This deletion retains hτ₂; the two swapping hypotheses cannot both be removed.

### [`P2MW.S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition.KSpec.cube_eq_neg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition.lean#L356-L585) — `flt-anthropic-0063`

Snippet: `samples/flt-anthropic/flt-anthropic-0063.lean`

- `(hF₁ : ∀ f ∈ F, J₁ f ∈ F)` (theorem): Recover it from h23: J₁ f = J₂ (J₃ f) - J₃ (J₂ f). Both terms belong to F by hF₂ and hF₃, so Submodule.sub_mem applies. Then reuse the original proof. This also covers F = ⊥.
- `(hF₂ : ∀ f ∈ F, J₂ f ∈ F)` (theorem): Recover it from h31: J₂ f = J₃ (J₁ f) - J₁ (J₃ f). Membership follows from hF₁, hF₃ and Submodule.sub_mem. Then reuse the original proof, including when F = ⊥.
- `(hF₃ : ∀ f ∈ F, J₃ f ∈ F)` (theorem): Recover it from h12: J₃ f = J₁ (J₂ f) - J₂ (J₁ f). Membership follows from hF₁, hF₂ and Submodule.sub_mem. Then reuse the original proof, including when F = ⊥.
- `(hskew₁ : ∀ x ∈ F, ∀ y ∈ F, B (J₁ x) y = -B x (J₁ y))` (theorem): The proof derives subtraction in both arguments of B solely from hlin and hsymm. Using those identities, h23 and the other two skew identities gives B (J₁ x) y = B x (J₃ (J₂ y)) - B x (J₂ (J₃ y)) = -B x (J₁ y). Invariance supplies every required membership. Recover hskew₁ before continuing the original proof; no nonzero assumption is needed.
- `(hskew₂ : ∀ x ∈ F, ∀ y ∈ F, B (J₂ x) y = -B x (J₂ y))` (theorem): Using the subtraction identities derived from hlin and hsymm, expand h31 and apply hskew₃ and hskew₁ twice: B (J₂ x) y = B x (J₁ (J₃ y)) - B x (J₃ (J₁ y)) = -B x (J₂ y). Invariance justifies all memberships. This recovers the deleted hypothesis even on the zero submodule, after which the original proof applies.
- `(hskew₃ : ∀ x ∈ F, ∀ y ∈ F, B (J₃ x) y = -B x (J₃ y))` (theorem): Using the subtraction identities derived from hlin and hsymm, expand h12 and apply hskew₁ and hskew₂ twice: B (J₃ x) y = B x (J₂ (J₁ y)) - B x (J₁ (J₂ y)) = -B x (J₃ y). Invariance justifies all memberships. This recovers the deleted hypothesis without any nonzero assumption, allowing the original proof to continue.

### [`P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.W8O.ramificationIndex_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.lean#L169-L198) — `flt-anthropic-0064`

Snippet: `samples/flt-anthropic/flt-anthropic-0064.lean`

- `[FiniteDimensional M E]` (variable): Avoid theta and use hrange directly. Put q = p ^ r > 0. RingHom.mem_fieldRange gives m with algebraMap M E m = π ^ q for a uniformizer π, so ord_npow and Place.ramificationIndex_le_ord give e ≤ q. Conversely, Place.exists_ord_eq_ramificationIndex gives m of order e; hrange gives x with algebraMap M E m = x ^ q. Thus e = q * w.ord x, and Place.ramificationIndex_pos implies w.ord x ≥ 1, giving q ≤ e. These Place lemmas require only integrality, supplied by the retained IsPurelyInseparable hypothesis. This includes r = 0; zero witnesses are excluded by positive order, and an empty Place type is vacuous.
- `[IsPurelyInseparable M E]` (variable): This follows from hrange. For every x : E, x ^ p ^ r belongs to the field range of iterateFrobenius, hence to the range of algebraMap M E by hrange and RingHom.mem_fieldRange. The checked lemma isPurelyInseparable_iff_pow_mem M p therefore constructs IsPurelyInseparable M E, using exponent r for every x. Install this as a local instance and retain the original proof. The construction also covers x = 0 and r = 0.
- `[CharP M p]` (variable): Recover it locally using (algebraMap M E).charP (algebraMap M E).injective p, by RingHom.charP and the retained CharP E p instance. Then the original proof applies unchanged. The statement itself uses Frobenius only on E, so it needs no CharP M p instance. Algebra maps between fields are injective, with no empty or trivial-field exception.

### [`P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.lean#L2414-L2438) — `flt-anthropic-0066`

Snippet: `samples/flt-anthropic/flt-anthropic-0066.lean`

- `(ha2 : a ^ (q ^ 2) = a)` (theorem): The existing proof works unchanged: ha2 is never used, and ModularCurve.C4b.core has no corresponding assumption. Thus the proof covers arbitrary a satisfying the remaining hypotheses.
- `(h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)` (theorem): Split on whether the reduction is zero. In the nonzero case, use the existing proof. In the zero case, Subtype.ext identifies the element in the conclusion with zero, and AlgebraicCurve.Place.ord_zero proves the result. This lemma is established in Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean; ord assigns zero to zero.

### [`P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.lean#L607-L672) — `flt-anthropic-0068`

Snippet: `samples/flt-anthropic/flt-anthropic-0068.lean`

- `(hσiso : IsIso σ.1)` (theorem): This follows from hpol and u's existing properties. Spec k has one point, so hpol gives σ* u.pol ≅ u.pol globally. The definitions give a very ample invertible sheaf on the smooth, proper, connected scheme u.A, which is integral. Preservation of this sheaf makes σ finite: a positive-dimensional fibre would carry a trivial very ample sheaf, which is impossible. A finite self-map of this integral variety is surjective. Pullback therefore acts injectively, hence bijectively, on the finite-dimensional space H⁰(u.pol). In the complete-linear-system embedding, σ is consequently induced by a projective linear automorphism, so it is a closed immersion. Since u.A is reduced and σ is surjective, `isIso_of_isClosedImmersion_of_surjective` gives IsIso σ.1. Supply this derived fact to the existing proof instead of hσiso. This argument also covers dimension zero; emptiness is excluded by the section u.L.one (𝟙 _), and no positivity assumptions on g, d, or n are needed.

### [`P2MW.S_CohCarrier_isEis_kernel_pair_of_prime.CohCarrier.IsEisKernelPairPrime.exists_crt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_isEis_kernel_pair_of_prime.lean#L359-L443) — `flt-anthropic-0072`

Snippet: `samples/flt-anthropic/flt-anthropic-0072.lean`

- `[NeZero P]` (theorem): Split on P = 0. In the nonzero case, install NeZero P and use the existing proof. If P = 0, Nat.coprime_zero_left forces M₁ = 1; choose g₁ = g. The first equality is reflexive, and the second follows from mapN_eq_iff since 1 divides every integer. mapN requires no nonzero hypothesis.
- `[NeZero M₁]` (theorem): Split on M₁ = 0. In the nonzero case, install NeZero M₁ and use the existing proof. If M₁ = 0, Nat.coprime_zero_right forces P = 1; choose g₁ = 1. The first equality follows from mapN_eq_iff since 1 divides every integer, and the second is map_one.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart_of_eq_three.B3Ends.sc_pow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart_of_eq_three.lean#L92-L93) — `flt-anthropic-0076`

Snippet: `samples/flt-anthropic/flt-anthropic-0076.lean`

- `[IsDomain (CoordRing q k)]` (variable): The same proof works with this instance omitted. `drinfeldFunctionField` is `FractionRing (CoordRing q k)`, whose commutative ring and k-algebra structures exist without a domain assumption; `sc` needs only these structures. `scalarOf_pow_of_mem` likewise has no domain assumption. Mapping its equality through the algebra map using `map_pow` and `map_one` proves the result, even for rings with zero divisors or a trivial target.

### [`P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd.LevelRaisingCornerDvdSol.heckeT_wL_eq_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd.lean#L429-L433) — `flt-anthropic-0077`

Snippet: `samples/flt-anthropic/flt-anthropic-0077.lean`

- `[NeZero N]` (variable): The statement elaborates without this instance: H1, LevelLE and the definition wL do not require it. Split on N = 0; the nonzero case uses the existing proof. At N = 0, iDeg' with parameter 1 is the identity, and direct matrix calculation gives iotaDeg_q ∘ conjL equal to subgroup inclusion. The source lemmas heckeT_card_smul_impl and IharaMintIdx.natCard_rightQuot in S_CohCarrier_heckeT_iDeg_q_eq_smul.lean require no nonzero level and give heckeT ∘ iDeg'_q = q • id (since q ∣ 0). Unfolding wL therefore reduces the conclusion to q • heckeT v - q • heckeT v = 0. This also works for the trivial coefficient ring; [NeZero q] remains available.

### [`P2MW.S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.lean#L36-L71) — `flt-anthropic-0083`

Snippet: `samples/flt-anthropic/flt-anthropic-0083.lean`

- `[NeZero N]` (theorem): The statement and proof do not need this instance. In Def_ModularCurve_X1.lean, x1FunctionField, x1FunctionFieldBar and JOne are defined for every natural level, including N = 0. The arithmeticGalois construction and Galois action work for any intermediate field, and the pairing lemmas require only the retained hypotheses on n and principal divisors. Thus the existing proof works unchanged after deleting [NeZero N], including at N = 0.

### [`P2MW.S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.Loc4Sol.residual_isEquiv_point`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.lean#L165-L200) — `flt-anthropic-0088`

Snippet: `samples/flt-anthropic/flt-anthropic-0088.lean`

- `(hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)` (theorem): Apply GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq with exceptional finset S ∪ N.primeFactors instead of S. Outside this union, nonmembership in S is immediate, and Nat.mem_primeFactors_of_ne_zero, using NeZero.ne N, gives ¬ ℓ ∣ N. The remaining proof is unchanged. This also works when S is empty or N = 1; N = 0 remains excluded.
- `(habs : ρbar.IsAbsolutelyIrreducible)` (theorem): The proof through hall does not use habs. Equal characteristic polynomials give equal traces for the two residual representations over ResidueField 𝒪'. By habs' and ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top, the first representation spans its full endomorphism algebra. Any linear relation among the second representation's operators is also a relation among the first: multiply by each group operator, compare traces, and use nondegeneracy of the matrix trace pairing (Matrix.ext_iff_trace_mul_left). Thus the second span surjects onto the first endomorphism algebra. Both representations have dimension 2, so both endomorphism algebras have dimension 4; consequently the second span is full too. The same equivalence lemma supplies its absolute irreducibility, allowing the original final step. This works in every characteristic, including 2. Here habs' must be retained; the two irreducibility assumptions cannot generally both be deleted.
- `(habs' : ρ'.residual.IsAbsolutelyIrreducible)` (theorem): The proof through hall does not use habs'. Retain habs.baseChangeAlong φk, which makes the second representation absolutely irreducible. As above, equal traces and nondegeneracy of the full matrix trace pairing yield a surjection from the first representation's operator span onto the second's full endomorphism algebra. Both spaces have dimension 2, hence their endomorphism algebras have dimension 4, forcing the first span to be full. ResidualGaloisRep.isAbsolutelyIrreducible_iff_span_eq_top then supplies habs', and the original final step applies. There is no zero-dimensional exception, and the trace pairing remains nondegenerate in characteristic 2. This deletion retains habs; the two irreducibility assumptions cannot generally both be deleted.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.K45VolB3.iterate_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.lean#L218-L220) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- `[NumberField L]` (variable): The same proof works after omitting this instance. The definition of sigmaTensor and the lemma sigmaTensor_pow require only [Field K], [Field L], [Algebra K L] and a commutative K-algebra A. For A = Kv, its structures depend on K and v, not on [NumberField L]. Thus the existing rewrites followed by map_mul remain valid for arbitrary field extensions L/K, including infinite ones; i = 0 is simply multiplicativity of the identity.

### [`P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD.pairF_res_cores_normal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_index_Gamma_four.lean#L5591-L5659) — `flt-anthropic-0095`

Snippet: `samples/flt-anthropic/flt-anthropic-0095.lean`

- `[Γ'.FiniteIndex]` (theorem): It follows from [Φ.FiniteIndex] and hΦΓ by Subgroup.finiteIndex_of_le. Delete the binder and start the proof with `haveI : Γ'.FiniteIndex := Subgroup.finiteIndex_of_le hΦΓ`; the remaining proof is unchanged. This implication has no nontriviality assumptions.
- `(hΦ1 : (-1 : SL(2, ℤ)) ∉ Φ)` (theorem): This follows from [IsFreeGroup Φ]. Choose a free group basis using IsFreeGroup.nonempty_basis. Its repr embeds Φ into a FreeGroup, whose torsion-freeness is established in Mathlib/GroupTheory/FreeGroup/CyclicallyReduced.lean. If -1 belonged to Φ, its square would be 1, so pow_eq_one_iff_left applied to its image would force it to equal 1. Comparing the (0,0) integer matrix entries gives -1 = 1, a contradiction. Derive hΦ1 locally and retain the original proof. This argument also covers trivial Φ and is independent of R.

### [`P2MW.S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.lean#L99-L202) — `flt-anthropic-0099`

Snippet: `samples/flt-anthropic/flt-anthropic-0099.lean`

- `[Fact p.Prime]` (theorem): Neither the remaining definitions nor the proof require primality. The argument uses only the curve model and finite exceptional sets, and works unchanged for every p satisfying the remaining assumptions.
- `[NeZero M]` (theorem): The definitions IntegralWeightOneForm, x1FunctionField and igusaFunctionFieldX1C do not require this instance, and the proof does not use it. Moreover, hM already excludes M = 0.
- `(hM : 5 ≤ M)` (theorem): No later binder or proof step uses hM. The same proof works at every level M for which the remaining data exist.
- `(hpM : ¬ p ∣ M)` (theorem): This hypothesis is unused in the remaining statement and proof. The finite-exceptional-set argument also applies when p divides M.
- `[IsCyclotomicExtension {p} ℚ L]` (theorem): No remaining construction or proof step uses cyclotomicity. The rational algebra needed by coeffEmb and laurentBaseChange remains available from Field L and CharZero L.
- `(hζ : IsPrimitiveRoot ζ p)` (theorem): No later binder or proof step references hζ. The proof works for arbitrary ζ satisfying the remaining assumptions.
- `(hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))` (theorem): The proof never uses this identification. It works for an arbitrary intermediate field K equipped with the remaining data.
- `[IsFractionRing A L]` (theorem): TwoChart.modelTo and TwoChart.ιFin require the specified algebra on K, not this fraction-ring property. Neither the remaining statement nor the proof uses it.
- `(hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)` (theorem): No later binder or proof step uses hAp. The argument is independent of whether p belongs to the maximal ideal.
- `(hζA : ∃ z : A, algebraMap A L z = ζ)` (theorem): The lift is never used, and no later binder depends on its proof. The supplied proof works without a lift of ζ.
- `[IsScalarTower A L ↥K]` (theorem): The two-chart definitions use Algebra A ↥K directly and do not require this tower compatibility. The proof never compares the two scalar actions.
- `(hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)` (theorem): This equality is unused. The proof works for arbitrary j with the retained Fact (j ≠ 0), so deleting hj introduces no zero-chart issue.
- `[CharP k p]` (theorem): IntegralWeightOneForm and igusaFunctionFieldX1C require only Field k. The curve-model lemmas used in the proof are characteristic-independent, so the same proof works without this instance.
- `[IsProper c₁]` (theorem): Properness needed in the proof is supplied by Mdl₁.isProper for Mdl₁.toBase, not by c₁. These model fields can be installed explicitly as local instances if necessary; all finiteness and nonemptiness arguments remain unchanged.
- `[SmoothOfRelativeDimension 1 c₁]` (theorem): The proof needs smoothness only for Mdl₁.toBase, supplied by Mdl₁.smooth. Neither SchemeHomOver nor the conclusion requires smoothness of c₁.
- `[GeometricallyIntegral c₁]` (theorem): The proof uses integrality of Mdl₁.C, supplied by Mdl₁.isIntegral. Its point equivalences and finite-complement argument require no geometric-integrality assumption on c₁.
- `[IsProper c₂]` (theorem): The proof uses C₂ only through the pullback and its projection. Finiteness of that pullback follows from hn and hn0, independently of properness.
- `[SmoothOfRelativeDimension 1 c₂]` (theorem): No construction in the remaining statement or proof requires this instance. The exceptional crossing set is finite by hn and hn0 alone.
- `[GeometricallyIntegral c₂]` (theorem): This instance is unused. The argument requires only the finite range of the pullback projection, obtained from hn and hn0, regardless of the geometry of C₂.
- `[IsClosedImmersion i₁.1]` (theorem): The pullback exists for arbitrary scheme morphisms. Its finite projection range follows from hn and hn0; the proof uses neither closedness nor injectivity of i₁.
- `[IsClosedImmersion i₂.1]` (theorem): The proof needs only finiteness of the pullback, supplied by hn and hn0. No step or remaining construction requires i₂ to be a closed immersion.
- `(hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)` (theorem): The covering assertion is never used. The proof works entirely on Mdl₁.C, using hn and hn0 for the crossing set and hne₁ for the nonempty chart preimage.
- `(hred : IsReduced (pullback i₁.1 i₂.1))` (theorem): Reducedness is unused. Only the underlying pullback's finiteness matters, and Nat.finite_of_card_ne_zero supplies it from hn and hn0 even for a nonreduced pullback.

### [`P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.R4GC.qC_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.lean#L1440-L1442) — `flt-anthropic-0104`

Snippet: `samples/flt-anthropic/flt-anthropic-0104.lean`

- `[NeZero m]` (variable): The definitions of Γ, GH, levelH and qC do not require this instance. Without it, establish one_mem_strictPeriods by the same argument using translation_mem_GammaH and Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem; neither requires a nonzero level. Then the original proof works using ModularForm.qExpansion_eq_zero_iff and HahnSeries.ofPowerSeries_injective. This also covers m = 0 and M' = 0.

### [`P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.R3M4Torus.ι₀_root`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.lean#L48-L49) — `flt-anthropic-0111`

Snippet: `samples/flt-anthropic/flt-anthropic-0111.lean`

- `[Fact (Irreducible γ₀.charpoly)]` (variable): Neither E nor ι₀ depends on irreducibility: they use the polynomial quotient and Cayley–Hamilton. AdjoinRoot.root is mk applied to X, and ι₀ evaluates quotient representatives at γ₀. After omitting this instance, a proof is `change Polynomial.aeval γ₀ Polynomial.X = γ₀; exact Polynomial.aeval_X`. This works for every γ₀, including zero and matrices with reducible characteristic polynomial.

### [`P2MW.S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.lean#L32-L223) — `flt-anthropic-0121`

Snippet: `samples/flt-anthropic/flt-anthropic-0121.lean`

- `(hpS : p ∈ S)` (theorem): Recover it as `hNS p (Fact.out : p.Prime) hpN`, exactly as the proof already constructs `hpinS`. Pass this derived proof instead of hpS to the jointly-injective-points theorem. This handles every case allowed by the remaining assumptions.
- `(hNp : ¬ p ^ 2 ∣ N)` (theorem): Recover it as `fun h => hθ'U (hU0 p (Fact.out : p.Prime) hpN (hNS₀ p Fact.out hpN) h)`, then use the existing proof. If p² divides N, hU0 makes precisely the U-value required nonzero by hθ'U equal zero, so that case is contradictory.
- `(hTp : ∀ (hpN : ¬ p ∣ N) (hpS₀ : p ∉ (↑S₀ : Set ℕ)), ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p → ∀ E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[ResidueField 𝒪] (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)), (∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) → θ' (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpN hpS₀) = LinearMap.trace (ResidueField 𝒪) _ E)` (theorem): The retained outer hpN proves p ∣ N, whereas hTp first assumes ¬ p ∣ N. Reconstruct hTp by `intro hnot; exact False.elim (hnot hpN)` and pass it to the jointly-injective-points theorem. Its entire domain is contradictory, regardless of the subsequent data.
- `(hθ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), θ t = θ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))` (theorem): Neither the proof nor any subsequent binder or conclusion uses hθ. The proof uses hΨ for compatibility instead and works unchanged after deleting hθ, with no additional exceptional cases.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.M4aD2Skeleton.zetaIntegral_eq_setIntegral_theta'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.lean#L6363-L6392) — `flt-anthropic-0122`

Snippet: `samples/flt-anthropic/flt-anthropic-0122.lean`

- `(hD'm : MeasurableSet D')` (theorem): Replace setIntegral_congr_fun hD'm with setIntegral_congr_fun₀ hD'.nullMeasurableSet. IsFundamentalDomain supplies null-measurability, and the remaining pointwise proof is unchanged. This also handles nonmeasurable fundamental domains and null sets.
- `[BorelSpace (AdeleRing (𝓞 F) F)]` (theorem): Only ideleNorm_mul_principal needs this instance in the proof. Prove its required equality locally using the measurable space borel (AdeleRing (𝓞 F) F) and BorelSpace instance ⟨rfl⟩. Its equality is independent of that choice: ideleNorm uses distribHaarChar, which internally chooses the Borel measurable space. The conclusion, schwartzBruhat, and ThetaSum do not use the additive adele measurable structure; integrable_zetaIntegrand requires only the retained idele instances. Thus the same proof works even when the supplied additive measurable space is not Borel.

### [`P2MW.S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.NumberField.AdelicFourier.GodementSiegelEstimate.real_bound`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.lean#L337-L423) — `flt-anthropic-0123`

Snippet: `samples/flt-anthropic/flt-anthropic-0123.lean`

- `(hC : 0 ≤ C)` (theorem): Split on 0 ≤ C. In that case, use the existing proof. Otherwise C ≤ 0; choose B = 0. All factors multiplying C are nonnegative: the squared terms are nonnegative, and r ≥ 1, α > 0, δ > 0 ensure the inverse powers and their minima with 1 are nonnegative, including when N = 0. Repeatedly applying mul_nonpos_of_nonpos_of_nonneg makes the left side ≤ 0, while the right side equals 0.

### [`P2MW.S_TateCurve_ks17_D3_exports.TateCurve.sum_mul_Fz_Fz_eq_sum_lines_nat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_ks17_D3_exports.lean#L108-L111) — `flt-anthropic-0124`

Snippet: `samples/flt-anthropic/flt-anthropic-0124.lean`

- `[IsUltrametricDist K]` (theorem): The proof at P2M/Sol/S_TateCurve_ks17_C3_exports.lean:230–244 applies TateCurve.sum_mul_Fz_eq_sum_lines_nat twice and rearranges finite sums algebraically. That lemma (Definitions/Def_TateCurve_DefectLines.lean:1349) requires only [NontriviallyNormedField K]. Neither Fz nor the conclusion requires ultrametricity. The same proof works without it, including empty S and N = 0: Fz_zero eliminates all zero-index terms. This and completeness can both be deleted.
- `[CompleteSpace K]` (theorem): Replace the export-projection proof with the finite-sum proof at P2M/Sol/S_TateCurve_ks17_C3_exports.lean:230–244. Its two applications of TateCurve.sum_mul_Fz_eq_sum_lines_nat require no completeness, and the remaining steps are ring rearrangements and finite-sum identities. Fz is defined using integer powers, not limits. Empty S, N = 0, and u or v equal to zero cause no difficulty; Fz_zero holds for every u. Both completeness and ultrametricity can be deleted together.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal.Ψ₂Sq_𝓦p_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L273-L277) — `flt-anthropic-0125`

Snippet: `samples/flt-anthropic/flt-anthropic-0125.lean`

- `(hp2 : p ≠ 2)` (theorem): The coefficient of degree 2 in Ψ₂Sq is b₂, which for 𝓦p p is (MvPolynomial.X 0)^2 + 4 * MvPolynomial.X 1. If Ψ₂Sq were zero, this coefficient would vanish. Applying MvPolynomial.eval with values ![1, 0, 0, 0, 0], using eval_X, gives 1 = 0 in ZMod p, contradicting primality (p ≥ 2). This replaces the degree-3 coefficient argument and works also for p = 2.

### [`P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.KcSemiLocalIwasawaHaar.mem_K_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean#L1008-L1009) — `flt-anthropic-0126`

Snippet: `samples/flt-anthropic/flt-anthropic-0126.lean`

- `[NumberField L]` (variable): Use `omit [NumberField L] in`; the same `Iff.rfl` proof works. `semiLocalIntegralSet` unfolds to `integralUnitsSet (semiLocalIntegers K L v)`, whose membership is definitionally the stated entrywise conditions. Neither definition requires `[NumberField L]` (the existing `one_mem_semiLocalIntegralSet` also explicitly omits it). This equivalence holds for every remaining field L, without finiteness or other exceptional-case assumptions.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.AlgebraicCurve.HolRingFGAux.exists_fin_generators`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.lean#L590-L610) — `flt-anthropic-0132`

Snippet: `samples/flt-anthropic/flt-anthropic-0132.lean`

- `(hN : N.Nonempty)` (theorem): Split on N.Nonempty, using the existing proof in the nonempty case. Otherwise N = ∅; choose n = 0 and the empty function z. Every everywhere-regular f lies in LSpace 0 by mem_lSpace_iff_ord and ord_nonneg_of_mem (including f = 0). IsCurveOver.exists_separating_transcendental supplies x and finite dimensionality over k⟮x⟯, so AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental identifies LSpace 0 with the range of algebraMap k K. Thus f belongs to Algebra.adjoin k (Set.range z) by Subalgebra.algebraMap_mem. The generator-regularity condition is vacuous.

### [`P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.MapsDvdSol.opFamily_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.lean#L343-L365) — `flt-anthropic-0134`

Snippet: `samples/flt-anthropic/flt-anthropic-0134.lean`

- `[IsDomain 𝒪]` (variable): The proof works unchanged without this instance. opFamily and heckeTL require only CommRing 𝒪; diamondL_top_eq_one also requires only CommRing 𝒪 and NeZero N. The commutation lemma heckeT_comm_of_prime requires only additive-group coefficients. Thus zero divisors cause no problem.
- `[CharZero 𝒪]` (variable): No step uses characteristic zero. The inspected definitions and lemmas opFamily, diamondL_top_eq_one, and heckeT_comm_of_prime impose no characteristic restriction, so the same proof handles positive characteristic.
- `[IsLocalRing 𝒪]` (variable): Locality is unused: the same proof uses only CommRing 𝒪 and NeZero N. In fact all three reported instances can be removed simultaneously. The argument works even for the zero ring, where every coefficient-valued homomorphism is zero.

### [`P2MW.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.ModularCurve.map_eval₂_aeval_toRingHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.lean#L18-L24) — `flt-anthropic-0137`

Snippet: `samples/flt-anthropic/flt-anthropic-0137.lean`

- `[Algebra ℤ A]` (theorem): Deleting this binder leaves the statement elaborating: Mathlib's Ring.toIntAlgebra supplies Algebra ℤ A from CommRing A. The existing proof works unchanged with this canonical instance. No nontriviality is required, so trivial rings are covered. Both algebra binders can also be deleted together.
- `[Algebra ℤ B]` (theorem): Deleting this binder leaves the statement elaborating: Ring.toIntAlgebra supplies Algebra ℤ B from CommRing B. The existing hom_eval₂ and polynomial ring-hom extensionality proof works unchanged, including for trivial rings. Both algebra binders can also be deleted together.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.C2Count.natCard_finPts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.lean#L214-L257) — `flt-anthropic-0143`

Snippet: `samples/flt-anthropic/flt-anthropic-0143.lean`

- `(hm : 0 < m)` (theorem): The local lemma not_dvd_of_coprime derives hpm : ¬ p ∣ m from hmp and [Fact p.Prime]. Thus m ≠ 0, since every natural number divides 0 (Nat.dvd_zero), and Nat.pos_of_ne_zero recovers hm. Insert this derivation after defining hpm; the remaining proof is unchanged. The excluded case m = 0 is therefore impossible under the remaining hypotheses.

### [`P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve.SmoothedFundamentalProof.finite_support_smul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.lean#L435-L442) — `flt-anthropic-0144`

Snippet: `samples/flt-anthropic/flt-anthropic-0144.lean`

- `[Γ.FiniteIndex]` (variable): smoothedFundamental is defined using finsum and requires no finite-index instance. Let f δ := puCut T (mob δ τ); hasFiniteSupport_puCut_mob proves its support S finite without this assumption. The existing cosetEquiv Γ identifies (q, γ) with q.out * γ, so the image of S under δ ↦ ((cosetEquiv Γ).symm δ).2 is finite. The desired support lies in this image: unfolding smoothedFundamental and using coe_smul and mob_mob, a nonzero value at γ implies some q has f (q.out * γ) ≠ 0, since otherwise finsum_eq_zero_of_forall_eq_zero makes the value zero. The inverse equivalence sends this element to (q, γ). This works for every subgroup, including infinite-index and trivial subgroups; empty support also causes no problem.

### [`P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.AlgebraicCurve.BaseChangeTwo.lhs_eq_rhs_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.lean#L327-L359) — `flt-anthropic-0149`

Snippet: `samples/flt-anthropic/flt-anthropic-0149.lean`

- `(hg : g ≠ 0)` (theorem): Split on g = 0. In the nonzero case, use the existing proof. If g = 0, Place.ord_zero (Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) makes hD imply D = 0 by Finsupp extensionality, including when there are no places. Both lhs and rhs are additive homomorphisms, so both send D = 0 to zero.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.P2mFlatIsog.ringKrullDim_stalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.lean#L246-L300) — `flt-anthropic-0150`

Snippet: `samples/flt-anthropic/flt-anthropic-0150.lean`

- `[LocallyOfFiniteType fX]` (theorem): IsFinite h implies LocallyOfFiniteType h, and locallyOfFiniteType_comp gives LocallyOfFiniteType (h ≫ fY). Replace exists_algebra_finiteType fX by exists_algebra_finiteType (h ≫ fY); the remaining proof is unchanged. No compatibility between fX and fY is needed. The chosen affine opens remain nonempty because they contain x and h.base x.
- `[IsIntegral Y]` (theorem): On the chosen affine opens write B = Γ(Y,V), A = Γ(X,h ⁻¹ᵁ V), and I = ker φ. A remains a domain. Surjectivity of h implies every prime of B contains I. Replace B by B/I: this is a finite-type K-domain, and the induced map B/I → A is integral and injective. Apply the existing height_comap_eq to that map. Quotienting by I preserves all prime heights, since Ideal.primeSpectrumQuotientOrderIsoZeroLocus identifies Spec(B/I) with all of Spec(B); use PrimeSpectrum.height_eq_orderHeight and Order.height_orderIso. The existing stalk-localization argument then finishes. This includes nonreduced Y; x ensures both affine opens are nonempty.

### [`P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.NumberTheory.kw_hjoint_normBasis_liftHom_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.lean#L674-L685) — `flt-anthropic-0151`

Snippet: `samples/flt-anthropic/flt-anthropic-0151.lean`

- `[CharZero F]` (variable): Use `omit [CharZero F] in` before the theorem; the existing proof still works. The definition `kw_hjoint_normBasis` uses only field operations and polynomial identities, and does not retain this instance. `Basis.liftHom` is defined by the four-term linear expression displayed in the proof, and `Matrix.algebraMap_matrix_apply` requires no characteristic assumption. Entrywise simplification and `ring` prove the identity in every characteristic, including characteristic two, and when any coefficients vanish.

### [`P2MW.S_CuspidalType_sum_character_mul_character_inv.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspidalType_sum_character_mul_character_inv.lean#L10-L30) — `flt-anthropic-0154`

Snippet: `samples/flt-anthropic/flt-anthropic-0154.lean`

- `[FiniteDimensional K V]` (theorem): The existing proof works without this binder. Representation.character is defined using LinearMap.trace without requiring finite dimensionality, and Representation.char_orthonormal has no finite-dimensionality hypothesis: it derives it internally from irreducibility and finiteness of the group. The construction of irreducibility uses only hirr and the retained Nontrivial V assumption.
- `[CharZero K]` (theorem): Split on whether n = (Nat.card (GL2 q) : K) is zero. If nonzero, the existing orthonormality argument applies. If zero, put τ = Representation.linHom ρ ρ and A = ∑ g, τ g. Reindexing multiplication in the finite group gives A² = n • A = 0. Thus LinearMap.isNilpotent_trace_of_isNilpotent shows trace A is nilpotent, hence zero in the field K. By linearity of trace and Representation.char_linHom, trace A is precisely the sum in the conclusion (using commutativity). Both sides therefore vanish in this formerly excluded case.

### [`P2MW.S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.K51A1.retr_tmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.lean#L38-L40) — `flt-anthropic-0160`

Snippet: `samples/flt-anthropic/flt-anthropic-0160.lean`

- `[FiniteDimensional K L]` (variable): Neither retr nor its defining proof requires finite dimensionality. After omitting this instance, the existing proof still works using LinearMap.rTensor_tmul and TensorProduct.lid_tmul. These identities hold for arbitrary extensions, including infinite-dimensional ones, and for zero inputs.
- `[IsTopologicalRing A]` (variable): retr is defined purely algebraically and does not require this instance. Omitting it leaves the statement well-formed and the existing proof unchanged: LinearMap.rTensor_tmul followed by TensorProduct.lid_tmul. No topological compatibility is needed, including when A is trivial.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.R4ODGlue.eq_of_proj_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.lean#L415-L421) — `flt-anthropic-0167`

Snippet: `samples/flt-anthropic/flt-anthropic-0167.lean`

- `(hcomm : q'.comp p' = q''.comp p'')` (variable): Apply hpb at (0, 0), whose compatibility follows from RingHom.map_zero without hcomm. Both 0 and b₁ - b₂ project to (0, 0), the latter by RingHom.map_sub and h', h''. Uniqueness therefore gives b₁ - b₂ = 0, hence b₁ = b₂. This argument also works for trivial rings and requires no nonzero assumptions.

### [`P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.KcSemiLocalIwasawaHaar.coe_nGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.lean#L1038-L1038) — `flt-anthropic-0168`

Snippet: `samples/flt-anthropic/flt-anthropic-0168.lean`

- `[NumberField L]` (variable): This instance is automatically included but unnecessary. The definition of nGL uses AutomorphicForm.unipotentGL2, which requires only a commutative ring and has underlying matrix definitionally !![1, x; 0, 1]. The tensor-product ring structure needs [Field L] and [Algebra K L], not [NumberField L]. Thus `omit [NumberField L] in` leaves the statement well-formed and the same `rfl` proof works. The identity holds for every x, including zero, without any finiteness assumption on L.

### [`P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData.V_eq_O`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.lean#L489-L504) — `flt-anthropic-0182`

Snippet: `samples/flt-anthropic/flt-anthropic-0182.lean`

- `[LocallyOfFiniteType f]` (variable): This follows from D. Each D.c k is a closed immersion, hence locally of finite type; awayι₀ is an open immersion, and ProjSpace.π is proper, hence locally of finite type. Composition and D.hover therefore give LocallyOfFiniteType ((D.U k).ι ≫ f). Apply IsZariskiLocalAtSource.of_iSup_eq_top with D.hcov, install the resulting instance, and use the original proof. This argument also handles an empty indexing type.
- `[QuasiCompact f]` (variable): Each D.U k is compact: D.c k is a closed embedding into an affine spectrum, so Topology.IsClosedEmbedding.compactSpace applies. D.hcov expresses X as a finite union of these compact opens, proving CompactSpace X. Since the target spectrum is quasi-separated, quasiCompact_of_compactSpace supplies QuasiCompact f, after which the original proof applies. The finite-union argument includes the empty-cover case.
- `[IsNoetherianRing A]` (variable): The needed auxiliary results can be reproved without noetherianity by replacing its compactness argument. The remaining QuasiCompact f gives CompactSpace X. Each D.U k is compact by its closed embedding D.c k; X is quasi-separated because f is separated over an affine scheme. Finite intersections are compact by IsCompact.inter_of_isOpen, so D.Uo is compact (the empty intersection is X). D.XP is quasi-separated, hence quasiCompact_of_compactSpace gives QuasiCompact D.ψ. This replaces the noetherian-space instance used in the auxiliary proofs; their image, reducedness, irreducibility, and immersion arguments then proceed unchanged, yielding the displayed proof.
- `[IsIntegral X]` (variable): Replace the reducedness and irreducibility arguments by schematic density. The remaining noetherian and finite-type assumptions still make D.ψ quasi-compact. Scheme.Hom.toImage_app_injective shows that D.ψ' is schematically dense, also after restriction to D.V k. Thus ak_eq_bk follows without reducedness: its closed equalizer contains this schematically dense restriction, so its defining ideal is zero. The subsequent closed-immersion and properness arguments for ek still apply. Finally, its range is closed in D.O k and contains the dense range of D.ψ', so it is all of D.O k; neither irreducibility nor nonemptiness is needed. If D.Uo is empty, dominance of D.ψ' forces D.X' to be empty, and the equality holds too.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.AlgebraicCurve.AlgebraicCurve.adeleBddPrincipal_eq_comap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean#L791-L793) — `flt-anthropic-0183`

Snippet: `samples/flt-anthropic/flt-anthropic-0183.lean`

- `[HasPrincipalDivisors K F]` (theorem): The definitions of adeleBddPrincipal, adeleBdd, globalSub and adeleSpace do not require this instance. Put S = adeleBdd D, T = globalSub K F and C = adeleSpace K F. Since adeleBdd_le_adeleSpace gives S ≤ C without this hypothesis, the modular identity gives C ⊓ (S ⊔ T) = S ⊔ (C ⊓ T). Apply Submodule.map_injective_of_injective to C.subtype, then use Submodule.map_sup and Submodule.map_comap_subtype to reduce the conclusion to this identity (sup_inf_assoc_of_le, with inf_comm). Thus T ≤ C is unnecessary. This argument also covers an empty Place type and zero submodules.

### [`P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE.ell_sub_eq_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.lean#L175-L187) — `flt-anthropic-0184`

Snippet: `samples/flt-anthropic/flt-anthropic-0184.lean`

- `(hf0 : f ≠ 0)` (theorem): Split on f = 0. In the nonzero case, use the existing proof. In the zero case, Place.ord_zero gives P v = 0 for every place by hP. Since Divisor K F is Place K F →₀ ℤ, extensionality yields P = 0, and the conclusion simplifies to reflexivity. This also works when the type of places is empty.

### [`P2MW.S_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel.GramAsm.pair_mem_degZero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel.lean#L238-L244) — `flt-anthropic-0191`

Snippet: `samples/flt-anthropic/flt-anthropic-0191.lean`

- `[Fact q.Prime]` (variable): The conclusion holds even when q = 0. For any nonzero level M, use deg_eq_one_modularFunctionFieldBar as in the original proof. At level 0, the definitions of divisorExpansions, modularFunctionFieldFull and laurentBaseChange show that modularFunctionFieldBar 0 is generated by the coefficient-embedded qExpand ℚ d jq for all nonzero d. Each generator is algebraic over the field generated by the embedded jq, by B2Deg.finiteDimensional_adjoin_jBar d in S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean. IntermediateField.isAlgebraic_adjoin therefore makes the whole extension algebraic. B2Deg.deg_eq_one_of_isAlgebraic_adjoin then gives degree one for every place at level 0 too. The original degree subtraction finishes. Thus primality is unnecessary; both reported hypotheses can also be removed together.
- `[NeZero N]` (variable): The field and divisor expressions in the statement do not require this instance. Removing it additionally permits N = 0. At level 0, modularFunctionFieldBar is generated by the embedded qExpand ℚ d jq for nonzero d; B2Deg.finiteDimensional_adjoin_jBar d makes each algebraic over the field generated by the embedded jq. IntermediateField.isAlgebraic_adjoin and B2Deg.deg_eq_one_of_isAlgebraic_adjoin give degree one for every place, including at this level. At nonzero levels, deg_eq_one_modularFunctionFieldBar applies directly. In either case, Divisor.degree_single and map_sub give degree 1 - 1 = 0. Both reported hypotheses can be removed together.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.eq_span_tInvChart_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L2727-L2734) — `flt-anthropic-0199`

Snippet: `samples/flt-anthropic/flt-anthropic-0199.lean`

- `(ht : Transcendental κ t)` (variable): The remaining hchartInv makes φ := aevalChart κ t⁻¹ surjective by aevalChart_surjective. The proper ideal 𝔮.comap φ contains X, since φ(X) = tInvChart κ t and h holds. The lemma isMaximal_span_X_sub_C at 0 shows that (X) is maximal, so Ideal.IsMaximal.eq_of_le and Ideal.comap_ne_top give 𝔮.comap φ = (X). Applying Ideal.map_comap_of_surjective and Ideal.map_span yields the required equality. This proof needs no injectivity or transcendence and works uniformly for algebraic t and t = 0; in the latter case hchartInv identifies the chart ring with the constants and the equality is 𝔮 = (0).

### [`P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.HeckeGammaH.sum_slash_beta_eq_heckeU_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean#L381-L463) — `flt-anthropic-0201`

Snippet: `samples/flt-anthropic/flt-anthropic-0201.lean`

- `(B : BezoutData M ℓ)` (theorem): B does not occur in the conclusion or other binders. By val_gamma0Units and the definition of Gamma0Map, hρ identifies ℓ with the value of the unit gamma0Units M ρ. ZMod.isUnit_prime_iff_not_dvd therefore gives ¬ ℓ ∣ M, and exists_bezoutData supplies B locally; the original proof then applies unchanged. This also covers M = 1, where ZMod M is trivial.
- `[NeZero M]` (variable): The remaining statement elaborates without this instance: quotient finiteness requires only NeZero ℓ, supplied by primality. Recover NeZero M locally from B: if M = 0, B.huv becomes B.u * ℓ = 1 in ℤ, forcing the positive natural ℓ to equal 1, contradicting primality. With this local instance, the original proof applies unchanged.

### [`P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.RoadA.coe_τ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.lean#L325-L326) — `flt-anthropic-0219`

Snippet: `samples/flt-anthropic/flt-anthropic-0219.lean`

- `[NeZero M]` (variable): Neither modularFunctionFieldBar M nor τ M σ requires NeZero M: modularFunctionFieldFull is defined for every natural M, and τ abbreviates arithmeticRingAut without using this instance. The instance is automatically included in the theorem but can be omitted using `omit [NeZero M] in`. The unchanged statement is still proved by `rfl`, since arithmeticRingAut applies coeffMap definitionally. This also holds for M = 0.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.R4TateModelKHb.Xc_def`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.lean#L362-L362) — `flt-anthropic-0230`

Snippet: `samples/flt-anthropic/flt-anthropic-0230.lean`

- `[CharZero L]` (variable): This instance is automatically included because L occurs in the statement, but Xc's definition uses only Field L. With `omit [CharZero L] in`, the same statement is still proved by `rfl`. LaurentSeries and HahnSeries.C require no characteristic-zero assumption. Even when (12 : L) = 0, both sides remain definitionally identical, using the field convention 0⁻¹ = 0.

### [`P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc.Bdd.mul_small`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PowerSeries_dvd_of_forall_taylorShift_order_le.lean#L132-L135) — `flt-anthropic-0231`

Snippet: `samples/flt-anthropic/flt-anthropic-0231.lean`

- `(hρ0 : 0 ≤ ρ)` (theorem): Split into cases. If m = 0, small_zero_iff makes both Small statements independent of ρ; apply Small.mul with ρ = 1. If C' = 0, hQ forces every coefficient of Q to vanish by norm_le_zero_iff, so Q = 0 by PowerSeries.ext and the conclusion holds for any ρ. Otherwise m > 0 and C' > 0: hQ (m - 1) gives 0 ≤ C' * ρ, since m - (m - 1) = 1. The lemma nonneg_of_mul_nonneg_right recovers 0 ≤ ρ, allowing the original proof.
- `(hC : 0 ≤ C)` (theorem): By the definition of Bdd, hP 0 gives ‖coeff 0 P‖ ≤ C. Combining this with norm_nonneg recovers hC, after which the original proof applies. This also covers P = 0 and C = 0.
- `(hC' : 0 ≤ C')` (theorem): By the definition of Small, hQ m simplifies to ‖coeff m Q‖ ≤ C', because m - m = 0 and ρ^0 = 1, including when ρ = 0. Combining this with norm_nonneg recovers hC', allowing the original proof.

### [`P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.EtaleCoordK1a.rankAtStalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean#L13-L24) — `flt-anthropic-0236`

Snippet: `samples/flt-anthropic/flt-anthropic-0236.lean`

- `[Module.FinitePresentation S M]` (theorem): In fact, both finite presentation and flatness can be deleted together. Unfold rankAtStalk at p directly. Since 0 belongs to p.asIdeal, every element of p.asIdeal.primeCompl is nonzero, hence a non-zero-divisor in the domain S. Apply IsLocalization.rank_eq and IsLocalizedModule.rank_eq with this complement to identify the localized rank with Module.rank S M. Then hrank and Module.finrank_eq_of_rank_eq finish. These lemmas require neither hypothesis and cover n = 0 and the zero module as well.
- `[Module.Flat S M]` (theorem): Flatness is unnecessary even without finite presentation: rankAtStalk is defined as the finrank of the localized module, not its residue-field fiber dimension. At any prime p, its complement consists of non-zero-divisors because S is a domain. IsLocalization.rank_eq followed by IsLocalizedModule.rank_eq therefore gives localized rank n from hrank; Module.finrank_eq_of_rank_eq gives the conclusion. This also works for torsion modules and n = 0.

### [`P2MW.S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.SupersingularTop3.mem_of_ord_nonneg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.lean#L40-L46) — `flt-anthropic-0240`

Snippet: `samples/flt-anthropic/flt-anthropic-0240.lean`

- `(hf : f ≠ 0)` (theorem): Split on whether f = 0. In the zero case, the conclusion follows from w.toValuationSubring.zero_mem (and Place.ord_zero confirms the order hypothesis holds). In the nonzero case, use the existing proof with the nonzero fact supplied by the case split.

### [`P2MW.S_RubinSilverberg_exists_polynomial_rsFamily.M4cP2.D52.PhiA_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_RubinSilverberg_exists_polynomial_rsFamily.lean#L410-L414) — `flt-anthropic-0247`

Snippet: `samples/flt-anthropic/flt-anthropic-0247.lean`

- `(hj : j < 21)` (theorem): First retain the given proof as an auxiliary result for j < 21. Over R = ℤ[X], form Q ∈ R[T] by replacing j in PhiPlusA j - PhiMinusA j with T, lifting the other inputs through Polynomial.C. The definitions show natDegree Q ≤ 20: lhsPairAG has degree at most 20 in T, and each hornerG expression has 21 coefficients. The auxiliary result gives Q.eval i = 0 for i = 0,…,20. These are distinct elements of the integral domain R, so Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero gives Q = 0. Evaluating at any natural j proves the unchanged conclusion without hj. This includes j = 0 and all j ≥ 21; the expressions use only polynomial operations, with no denominator or other exceptional cases.

### [`P2MW.S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.lean#L16-L30) — `flt-anthropic-0249`

Snippet: `samples/flt-anthropic/flt-anthropic-0249.lean`

- `[W.IsElliptic]` (theorem): The existing proof works unchanged without this instance. IsTwoKernel requires only the three displayed polynomial conditions, and eval_Psi2Sq_of_two_nsmul_eq_zero assumes no ellipticity. Affine.Point consists of nonsingular points and has an AddCommGroup instance even for singular curves. The zero point is excluded by hQ, so its default coordinates introduce no exceptional case.

### [`P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.R4RRN.FF_slash_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.lean#L366-L368) — `flt-anthropic-0250`

Snippet: `samples/flt-anthropic/flt-anthropic-0250.lean`

- `[NeZero M']` (variable): Neither FF nor its defining restriction and translation requires this instance. After `omit [NeZero M'] in`, unfold the coercion of FF to `⇑f ∣[k] (Dr q)⁻¹`; then `conjElem_eq`, `SlashAction.slash_mul`, and group cancellation prove the identity. This avoids the automatically restricted intermediate theorem. The case M' = 0 also works: coprimality forces q = 1, and the same group-action calculation applies.

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.QMHecke12.exists_generator`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.lean#L368-L422) — `flt-anthropic-0252`

Snippet: `samples/flt-anthropic/flt-anthropic-0252.lean`

- `(hι : Function.Injective ι)` (variable): Remove hι from the include command; the existing proof works unchanged. It obtains injectivity of qmPeriodMap from QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span, whose statement requires no injectivity assumption on ι. Its nonzero-parameter hypotheses follow from ne_zero_of_hB hB, so degenerate parameters are already excluded independently. No other step uses hι, and the statement does not depend on it.

### [`P2MW.S_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction.P2MMultE.β_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction.lean#L1110-L1113) — `flt-anthropic-0258`

Snippet: `samples/flt-anthropic/flt-anthropic-0258.lean`

- `[IsNoetherianRing O]` (variable): Mathlib's instance PrincipalIdealRing.isNoetherianRing derives this from the retained [IsPrincipalIdealRing O]. Thus omitting this variable leaves the statement elaboratable and the existing proof unchanged. The implication has no additional nontriviality assumptions, so no degenerate cases are introduced.

### [`P2MW.S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.AlgebraicCurve.AlgebraicCurve.Place.stichtenothGenusExists_of_isFractionRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean#L2159-L2166) — `flt-anthropic-0261`

Snippet: `samples/flt-anthropic/flt-anthropic-0261.lean`

- `[HasPrincipalDivisors K F]` (variable): IsCurveOver extends HasPrincipalDivisors, so the retained [IsCurveOver K F] supplies this instance. The original proof works using that parent instance.
- `[Nonempty (Place K F)]` (theorem): First construct P : PoleDivisorPackage K F using hasPoleDivisorPackage_of_isFractionRing, which needs no nonemptiness assumption. Its fields give degree P.B = P.n and 0 < P.n. If Place K F were empty, every divisor would be zero and have degree zero, a contradiction. Install the resulting Nonempty instance and apply the original genus-existence lemma.
- `[FiniteDimensional K (LSpace (0 : Divisor K F))]` (theorem): Choose a place v using the retained Nonempty assumption. Reduction at v defines a K-linear map from LSpace 0 to v.ResidueField. Its kernel is LSpace (-Finsupp.single v 1), using mem_lSpace_iff_ord and Place.mk_mem_maximalIdeal_iff. This space is zero by lSpace_eq_bot_of_degree_neg: degree (-single v 1) = -v.deg < 0, since one_le_deg applies under IsCurveOver. Thus reduction is injective. IsCurveOver.finite_residueField and FiniteDimensional.of_injective supply the deleted instance, after which the original proof applies. Zero elements are included in the kernel argument.
- `[IsDomain A]` (theorem): IsFractionRing A E does not require IsDomain A. Since E is a field, IsFractionRing.isDomain_iff_isField implies IsDomain A. Recover this instance locally and use the original proof. In particular, a trivial A is excluded by its injective fraction-ring map into the nontrivial field E.
- `[IsScalarTower A E F]` (theorem): Neither T, hA nor the conclusion depends on the supplied Algebra A F structure. Locally replace that structure by ((algebraMap E F).comp (algebraMap A E)).toAlgebra. IsScalarTower.of_algebraMap_eq (fun _ => rfl) supplies compatibility for this composite structure, and the original proof then applies without changing the statement. This construction works for every remaining set of hypotheses.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.WeierstrassCurve.WeierstrassCurve.ModularCurve.kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean#L3405-L3408) — `flt-anthropic-0263`

Snippet: `samples/flt-anthropic/flt-anthropic-0263.lean`

- `[W.IsElliptic]` (variable): Neither the remaining statement nor the proof needs ellipticity. The source lemma transcendental_polyToFunctionField_X holds for every affine Weierstrass curve over a field, including singular curves, using polyToFunctionField_injective.
- `[CharZero F]` (variable): The existing proof works unchanged: Transcendental.of_tower_top and transcendental_polyToFunctionField_X require no characteristic-zero assumption. The polynomial-injectivity argument has no characteristic-dependent exceptional case.
- `[CharZero F']` (variable): Neither lemma in the existing proof requires characteristic zero. Transcendence over F' follows from polyToFunctionField_injective for an arbitrary field, then descends to F.
- `[IsScalarTower R₀ F F']` (variable): The proof only needs the natural tower F → F' → (W⁄F').FunctionField, obtained from Algebra F F' and the function-field algebra. Compatibility with R₀ is unnecessary; the same argument works even without that compatibility.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]` (variable): No remaining binder depends on this centredness instance, and the existing proof never uses it. Transcendence follows solely from polynomial injectivity and restriction of scalars, regardless of centredness.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]` (variable): This instance is absent from the conclusion and unused by both proof lemmas. The existing proof works unchanged without any assertion about principal divisors.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]` (variable): No remaining binder depends on this centredness instance. The source transcendence lemma uses polyToFunctionField_injective, not places or centredness, so the existing proof remains valid without it.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]` (variable): The existing proof does not use this instance: transcendental_polyToFunctionField_X applies to any affine Weierstrass curve over a field, and Transcendental.of_tower_top then gives the conclusion. No divisor-theoretic assumption or exceptional-case argument is needed.

### [`P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.lean#L229-L413) — `flt-anthropic-0266`

Snippet: `samples/flt-anthropic/flt-anthropic-0266.lean`

- `[Finite G]` (theorem): Finiteness is only needed by the auxiliary coverage lemmas through range_ι_comp_eq_univ. In that proof, replace the argument that W is closed by observing that π.base '' W = π.base '' U, which is closed because π.isClosedMap and hUcl. W remains open for an arbitrary group, so its complement has closed image as before. The remaining argument and downstream coverage lemmas work unchanged without finiteness. No enumeration or finite union is then needed, including for infinite G.
- `(hsurj : Function.Surjective π.base)` (theorem): This follows from hsec and IsFinite π. The range of π.base is closed since π.isClosedMap. If its open complement V were nonempty, π ⁻¹ᵁ V would be empty, so its section ring would be subsingleton (the instance for Γ(C, ⊥) in Scheme.lean). Injectivity hsec V would force Γ(X, V) to be subsingleton, contradicting Scheme.component_nontrivial for nonempty V. Thus π.base is surjective, and the original proof applies. This argument handles empty schemes as well and does not require Finite G; both reported hypotheses can be deleted together.

### [`P2MW.S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.lean#L203-L596) — `flt-anthropic-0267`

Snippet: `samples/flt-anthropic/flt-anthropic-0267.lean`

- `(htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)` (theorem): Neither the remaining statement nor the proof uses htame. Deleting it leaves the existing proof unchanged, including when the quantified set is empty.
- `(hrN : ¬ r ∣ N * p)` (theorem): Recover hrN locally: Nat.Prime.dvd_mul applied to hr splits r ∣ N * p into r ∣ N or r ∣ p. In the second case, transitivity with hpN also gives r ∣ N. Either case gives hNS r hr ‹r ∣ N› : r ∈ S, contradicting hrS. The existing proof then applies unchanged. This argument requires no additional nonzero assumptions.

### [`P2MW.S_Function_orbitCensus_of_dihedralThree_relations.P2MKcOrbitCensus.b_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean#L14-L17) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- `[Fintype X]` (variable): The existing proof works unchanged without finiteness: applying b twice to b x = b y and rewriting with hb gives x = y. This works for every type X, including empty types.
- `[DecidableEq X]` (variable): The existing proof uses only congrArg and rewriting with hb; neither requires decidable equality. Function.Injective also requires no such instance. Both instance hypotheses can be removed simultaneously.

### [`P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.KcHaarQuotientMulRight.lintegral_density_mul_comp_mul_right_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.lean#L75-L109) — `flt-anthropic-0270`

Snippet: `samples/flt-anthropic/flt-anthropic-0270.lean`

- `[LocallyCompactSpace G]` (theorem): Split on whether G is locally compact. In the positive case, install the instance and use the existing proof. Otherwise, the guard in HaarQuotient.weight must be false: a topological group is regular (IsTopologicalGroup.regularSpace), hence R₁, and WeaklyLocallyCompactSpace.locallyCompactSpace would imply local compactness. Thus weight and density are identically zero; ENNReal.zero_div handles even the zero denominator. Both integrals are therefore zero, for arbitrary f and μ.
- `[SFinite μH]` (theorem): The remaining assumptions imply this instance. Local compactness and second countability make G sigma-compact; hH.sigmaCompactSpace then makes H sigma-compact. IsHaarMeasure supplies IsFiniteMeasureOnCompacts μH, so SigmaFinite.of_isFiniteMeasureOnCompacts gives SigmaFinite μH and the standard instance gives SFinite μH. Install these instances and retain the existing proof. This argument also covers trivial groups.

### [`P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.UqNSol.fstDiv_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean#L358-L366) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- `[hqN : Fact (¬ q ∣ N)]` (variable): Neither PlaceSpecialization nor fstDiv requires this instance. Since fstDiv is Finsupp.filter P.IsStrictFst, after omitting hqN a proof is `by classical; unfold PlaceSpecialization.fstDiv; exact Finsupp.filter_sum s f`. This filtering identity holds for every predicate, including when q divides N and when s or the index type is empty.

### [`P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.LCMazur.OrdQ.span_singleton_eq_range_ordProj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.lean#L263-L272) — `flt-anthropic-0275`

Snippet: `samples/flt-anthropic/flt-anthropic-0275.lean`

- `(h2 : finrank A V = 2)` (theorem): This follows from hφ. IsLocalRing supplies Nontrivial A, and LinearMap.charpoly_natDegree identifies the characteristic polynomial's natural degree with finrank A V. Polynomial.Monic.natDegree_mul, monic_X_sub_C, and natDegree_X_sub_C show that the right-hand side of hφ has natural degree 2. Recover h2 this way and use the original proof.
- `[IsLocalRing A]` (variable): A direct coordinate proof avoids locality. For nontrivial A, choose b := Module.finBasisOfFinrankEq A V h2 and put ψ = φ - β • 1. By hw, choose c₀,c₁ with ψ(b i) = cᵢ • w. Write xᵢ = b.repr w i. Comparing characteristic-polynomial coefficients using LinearMap.charpoly_toMatrix and Matrix.charpoly_fin_two gives c₀*x₀ + c₁*x₁ = α - β. Expanding w in the basis therefore gives ψ w = (α - β) • w. By hu and Ring.inverse_mul_cancel, ordProj φ α β fixes w, proving span w ≤ range. The reverse inclusion is exactly the original argument using hw. If A is subsingleton, V is subsingleton and the equality is automatic.

### [`P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.lean#L27-L40) — `flt-anthropic-0278`

Snippet: `samples/flt-anthropic/flt-anthropic-0278.lean`

- `(ha : a ≠ 0)` (theorem): Split on a = 0. In the nonzero case, the existing proof applies unchanged. When a = 0, AbsoluteValue.map_zero gives μ a = 0 < 1, and ⟨a, haA⟩ is zero in A, which belongs to its maximal ideal by Ideal.zero_mem. Thus the equivalence also holds at zero.

### [`P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.TH1Wanted2.inv_mem_and_const_mem_of_gaussPresentation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.lean#L874-L964) — `flt-anthropic-0285`

Snippet: `samples/flt-anthropic/flt-anthropic-0285.lean`

- `(hq3 : q = 3)` (theorem): The proof never uses hq3 and works unchanged for every prime q. The retained primality instance ensures q is nonzero, as required by qExpand and qExpand_injective.
- `(hqM' : ¬ q ∣ M')` (theorem): Neither the remaining statement nor the proof uses hqM'. The same Laurent-series witnesses work when q divides M'; the required nonzero assumptions remain.
- `(hK₁ : FiniteDimensional ↥k₀ ↥K₁)` (theorem): This hypothesis is unused. The proof of constant membership uses only halg and hA₁, and works for infinite-dimensional K₁ as well.
- `(IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →` (theorem): Introduced as hK1, this hypothesis is never used or referenced by subsequent binders. Remove its introduction; the remaining proof works unchanged, including for proper suprema.
- `(∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' → ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) → LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) →` (theorem): Introduced as hLD, this hypothesis is unused throughout the proof and subsequent statement. Deleting it and its introduction leaves the proof unchanged; no linear-independence or finite-family argument is needed.
- `(∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀) →` (theorem): Introduced as hRAT, this hypothesis is unused and has no subsequent dependencies. The proof establishes membership directly from hO, so it needs no condition placing rational Laurent series in F₀.
- `[Fact (j₁ ≠ 0)]` (theorem): Remove hjt0 and prove hjq0 directly: coeffEmb (AlgebraicClosure ℚ) jq equals jqModC (AlgebraicClosure ℚ) by the definitions and map_jqModC. Its coefficient at −1 is 1 by ModularCurve.coeff_jqModC_neg_one, so it cannot be zero. The remaining proof is unchanged. Thus hj₁ already excludes j₁ = 0 without this instance.

### [`P2MW.S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.P2mConormLSpace.CFE.trace_algebraMap'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.lean#L193-L203) — `flt-anthropic-0287`

Snippet: `samples/flt-anthropic/flt-anthropic-0287.lean`

- `[Algebra.IsSeparable K K']` (variable): Split on separability. The separable case uses the existing proof. Otherwise F'/F is also nonseparable: if it were separable, minpoly_algebraMap_eq_map hconst and Polynomial.separable_map would show every element of K' separable over K. Thus Algebra.trace_eq_zero_of_not_isSeparable makes both traces zero. This includes positive-characteristic inseparable cases.
- `[FiniteDimensional K K']` (variable): Split on finite dimensionality, retaining separability. The finite case uses the existing proof. In the infinite case, K'/K is algebraic and has finite separable subextensions of arbitrarily large degree (generate fields from finite independent families, using IntermediateField.finiteDimensional_adjoin). For each such extension, its primitive generator and minpoly_algebraMap_eq_map hconst preserve that degree over F. By minpoly.natDegree_le, F'/F therefore cannot be finite-dimensional. Both traces are then zero by Algebra.trace_eq_zero_of_not_exists_basis. These two reported hypotheses cannot both be deleted: take K'=F=F'=K(t), where hgen and hconst hold but the left trace is the identity and the right trace is zero.

### [`P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.lean#L110-L138) — `flt-anthropic-0294`

Snippet: `samples/flt-anthropic/flt-anthropic-0294.lean`

- `[IsDomain A]` (theorem): The remaining statement elaborates without this instance. IsFractionRing.injective A K requires no domain assumption and embeds A into the field K. Thus add `haveI : IsDomain A := Function.Injective.isDomain (algebraMap A K) (IsFractionRing.injective A K)` and retain the original proof. Injectivity into a field also excludes the trivial-ring case.

### [`P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.WNormSwapSol.θ_θ_γel`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.lean#L941-L962) — `flt-anthropic-0295`

Snippet: `samples/flt-anthropic/flt-anthropic-0295.lean`

- `(hpM2 : ¬ p ^ 2 ∣ M)` (variable): This follows from hd: the unit ZMod.unitsMap (...) d shows that p is a unit modulo M / p. By ZMod.isUnit_prime_iff_not_dvd, p does not divide M / p. Nat.dvd_div_iff_mul_dvd hpM, together with pow_two, then gives ¬ p ^ 2 ∣ M. Reconstruct hpM2 and retain the existing proof. This also covers M / p = 1.
- `(hζ : IsPrimitiveRoot ζ p)` (variable): Neither ζ nor hζ occurs in the conclusion or other hypotheses. Since p is prime and Qb is an algebraically closed field of characteristic zero, AlgebraicClosure.hasEnoughRootsOfUnity and HasEnoughRootsOfUnity.exists_isPrimitiveRoot supply a primitive pth root locally. Convert it to a unit using IsPrimitiveRoot.isUnit_unit and run the existing proof with this root instead. Primality ensures p ≠ 0. This deletion and the deletion of hpM2 can be made together.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.AlgebraicCurve.DiscRigidity.sum_filter_eq_of_degreeOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.lean#L80-L105) — `flt-anthropic-0299`

Snippet: `samples/flt-anthropic/flt-anthropic-0299.lean`

- `(hf : f ≠ 0)` (theorem): Split on f = 0. In the zero case, Place.ord_zero (Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) and hDf give Df v = 0 for every v, hence Df = 0 by Finsupp extensionality; both sums are zero, including for empty sets. In the nonzero case, the existing proof applies unchanged.


## Formal Frontier (17 flagged)

### [`GradedRing.Veronese.adjoin_component_one_eq_top`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseDegreeOne.lean#L80-L104) — `formal-frontier-0005`

Snippet: `samples/formal-frontier/formal-frontier-0005.lean`

- `(hn : 0 < n)` (theorem): Split into n = 0 and 0 < n; the positive case uses the existing proof. For n = 0, VeroneseZero.lean proves of_zero_eq_algebraMap_mul_pow: every direct-sum generator is a degree-zero coefficient times a power of zeroVariable. By its definition and mem_component_iff, zeroVariable belongs to component 𝒮 0 1, hence to its algebraic adjoin. Closure under powers, multiplication and addition therefore puts every element in that adjoin. This proves the zero case without hgen, including when S is the trivial ring. Importing VeroneseZero supplies the cited identity.

### [`Nat.DivisionGrowth.affine_lower_bound`](https://github.com/FormalFrontier/sequence-growth/blob/7b7db3df8a043a09d037de4ff1eced6873404fb2/SequenceGrowth/Data/Nat/DivisionGrowth.lean#L68-L94) — `formal-frontier-0117`

Snippet: `samples/formal-frontier/formal-frontier-0117.lean`

- `(hs : 0 < s)` (theorem): Split using Nat.eq_zero_or_pos s. For positive s, use the existing proof. When s = 0, Nat.zero_sub_one, div_zero and zero_div make both the ratio and offset zero. For m = 0 the conclusion is equality; for m > 0, zero_pow reduces it to 0 ≤ (u m : ℚ), proved by positivity. Thus the zero case requires no recurrence assumption, and hs can be deleted.

### [`AlgebraicGeometry.reducedIdentityComponent_topologicalKrullDim`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/Dimension.lean#L265-L296) — `formal-frontier-0126`

Snippet: `samples/formal-frontier/formal-frontier-0126.lean`

- `[IsAlgClosed K]` (variable): Replace the call to identityComponent_topologicalKrullDim by a dimension sandwich. Let H be the reduction and U its identity component. The retained hypotheses give H a group structure and a locally finite-type structure morphism. ringKrullDim_stalk_unit_eq_topologicalKrullDim, which requires only [Field K], identifies dim H with its stalk dimension at the unit. The unit belongs to U, and ringKrullDim_stalk_eq_coheight and coheight_eq_of_isOpenImmersion identify this with the coheight of that point in U. Order.coheight_le_krullDim gives dim H ≤ dim U; the inducing inclusion gives the reverse inequality. Finish with Scheme.reduction_topologicalKrullDim as before. These inequalities also cover infinite dimension, and the unit ensures H and U are nonempty. No algebraic closure is needed to elaborate the conclusion.

### [`SpectralStoneDuality.chosenLimitCylinder_subset_iff_eventually`](https://github.com/FormalFrontier/spectral-stone-duality/blob/78b803577679fc37120fa3406833af653fe12018/SpectralStoneDuality/LimitCylinderDescent.lean#L251-L261) — `formal-frontier-0141`

Snippet: `samples/formal-frontier/formal-frontier-0141.lean`

- `[HasLimit F]` (theorem): Mathlib's TopCat.topCat_hasLimitsOfSize supplies limits for this diagram: UnivLE.{v, max v u} is inferred. Thus HasLimit F is synthesized without this binder, the statement still elaborates, and the existing proof works unchanged. This also covers empty stages and empty limits; no nonemptiness assumption is required.

### [`CategoryTheory.CartesianMonoidalCategory.tensorLeftIsoProd_hom_app_fst`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/SingleCoverGroup.lean#L58-L63) — `formal-frontier-0146`

Snippet: `samples/formal-frontier/formal-frontier-0146.lean`

- `[HasBinaryProducts K]` (variable): CartesianMonoidalCategory already supplies a HasFiniteProducts instance (Cartesian/Basic.lean), and hasLimitsOfShape_discrete supplies HasBinaryProducts because WalkingPair is finite. Thus `omit [HasBinaryProducts K] in` leaves the statement elaborating and the existing proof valid. HasBinaryProducts is Prop-valued, so proof irrelevance preserves the chosen-product expressions. No additional nonemptiness or nontriviality assumption is needed.

### [`IsKrasner.adjoin_rootSet_le_adjoin_rootSet_of_norm_coeff_sub_lt`](https://github.com/FormalFrontier/polynomial-root-stability/blob/ceae7822f6151ec6626678db1653054d3398cff3/PolynomialRootStability/Krasner.lean#L363-L391) — `formal-frontier-0152`

Snippet: `samples/formal-frontier/formal-frontier-0152.lean`

- `(hε : 0 < ε)` (theorem): Recover it as `(norm_nonneg (g.coeff 0 - f.coeff 0)).trans_lt (hcoeff 0)`, then use the existing proof unchanged. Thus ε ≤ 0 is already excluded by hcoeff, including for constant polynomials.
- `(hfm : f.Monic)` (theorem): In Approximation.lean, the proof of the root-continuity estimate uses f.Monic only to establish f.natDegree ≠ 0 when f has the selected root. Replace that step using Polynomial.natDegree_pos_of_aeval_root, hfsep.ne_zero, the root equation, and injectivity of the field algebra map. Every other step of that estimate, its extension-field version, and the remaining Krasner argument is unchanged. Nonzero constants have no roots, so their case is vacuous. This deletion retains hdeg; hfm and hdeg cannot generally both be deleted.
- `(hdeg : g.natDegree = f.natDegree)` (theorem): Split on ε ≤ 1. In that case, unequal degrees contradict hcoeff at the larger degree: Polynomial.Monic.coeff_natDegree and Polynomial.coeff_eq_zero_of_natDegree_lt make the coefficient-difference norm equal to 1. Recover hdeg and use the existing proof. If ε > 1, Real.one_le_rpow shows the displayed radius is at least ‖x‖, even when the inverse exponent is zero. Thus hbound implies the Krasner inequality with y = 0. As in the existing rootwise argument, hfsep and hfsplit supply separability and splitting of minpoly K₀ x. IsKrasner.krasner then puts every reference root in K₀⟮0⟯ = ⊥, proving the inclusion regardless of g. Empty root sets are vacuous. This deletion retains hfm; the two cannot generally both be deleted.

### [`Subgroup.exists_continuous_coset_representative`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ContinuousCosetRepresentative.lean#L55-L74) — `formal-frontier-0160`

Snippet: `samples/formal-frontier/formal-frontier-0160.lean`

- `[T2Space G]` (variable): It follows from the remaining assumptions. Mathlib's TotallyDisconnectedSpace.t1Space supplies T1Space G, hence isClosed_singleton gives IsClosed ({1} : Set G). Then IsTopologicalGroup.t2Space_iff_one_closed supplies T2Space G. Recover this instance locally and use the existing proof unchanged. These implications also hold for the trivial group; no additional nontriviality assumption is needed.

### [`MvPowerSeries.isUnit_adicallyRestricted_iff_coeff_radical`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean#L83-L92) — `formal-frontier-0162`

Snippet: `samples/formal-frontier/formal-frontier-0162.lean`

- `[IsAdicComplete I R]` (variable): The criterion holds without completeness. Forward: map a unit through constantCoeff and adicReduction I 1; MvPolynomial.isUnit_iff gives nilpotence of the nonconstant coefficients modulo I, equivalently radical membership. Backward: MvPowerSeries.isUnit_iff_constantCoeff supplies a formal inverse g. For every k, the polynomial adicReduction I k f is a unit by MvPolynomial.isUnit_iff: its constant coefficient is a unit, and a^m ∈ I implies a^(m*k) ∈ I^k by Ideal.pow_mem_pow, so every nonconstant coefficient is nilpotent modulo I^k. Uniqueness of inverses identifies the reduction of g with this polynomial's inverse. Thus isAdicallyRestricted_iff_map_mem_poly_range shows g is restricted, proving f is a unit in the subring. This argument also handles k = 0 (the zero quotient), I = ⊤, trivial rings, and empty variable types.

### [`FundamentalGroup.existsUnique_hom_of_isOpenCover`](https://github.com/FormalFrontier/fundamental-groupoids/blob/2fdb99858e3feb7a6a06ae10915f286364de2cc1/FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean#L404-L527) — `formal-frontier-0164`

Snippet: `samples/formal-frontier/formal-frontier-0164.lean`

- `(hU : IsPathConnected (U : Set X))` (theorem): Both hU and hV can be deleted, even simultaneously. Replace each chart's frame functor by a componentwise version: on the basepoint's path component use chosen arrows and φU or φV; on every other component send all arrows to 1. Choose the arrows on the intersection using intersectionArrow, which requires only hI. These functors agree on the intersection by hcompat, so FundamentalGroupoid.descOfIsOpenCover and inclusion_comp_descOfIsOpenCover give the required homomorphism. For uniqueness, subdivide any based loop into chart-contained pieces, as in morphismProperty_of_isOpenCover, and merge consecutive pieces in the same chart. All remaining endpoints lie in the intersection. Closing each piece using intersection paths expresses the loop as a product of images of based chart loops; Path.Homotopic.concat_subpath justifies the subdivision equality. Thus the restrictions determine the homomorphism. The point p guarantees a nonempty intersection; additional path components and trivial groups cause no exceptions.
- `(hV : IsPathConnected (V : Set X))` (theorem): The same componentwise-frame construction and loop-subdivision argument described for hU works symmetrically without hV. Only the intersection needs paths from p to transition points. Components of V not containing p receive the trivial functor and do not affect based loops. The point p excludes an empty intersection, and the construction also works for trivial target groups. Both hU and hV may be deleted simultaneously.

### [`GradedRing.Veronese.finiteType_of_finiteType`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseFiniteType.lean#L105-L126) — `formal-frontier-0179`

Snippet: `samples/formal-frontier/formal-frontier-0179.lean`

- `(hn : 0 < n)` (theorem): Split into n = 0 and n > 0. The positive case uses the existing proof. For zero, `GradedRing.Veronese.finiteType_zero` in `GradedRings/VeroneseZero.lean` proves exactly the required conclusion without additional assumptions: the external direct sum is generated over its degree-zero component by its degree-one copy of 1. This also covers trivial rings.

### [`AlgebraicGeometry.Proj.degreeScaledChartMap_preimage_basicOpen`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/DegreeScaledMap.lean#L453-L469) — `formal-frontier-0188`

Snippet: `samples/formal-frontier/formal-frontier-0188.lean`

- `(hn : 0 < n)` (theorem): Only n = 0 needs a new argument. Put a = (i.2 : A). At a chart point, let P be its image prime and Q its ambient prime. The existing positive-degree proof gives a ∈ P ↔ f a ∈ Q, so a ∉ P since f a ∉ Q. Apply that proof to r*a, homogeneous of positive degree i.1. Primality and map_mul then cancel a and f a, giving r ∈ P ↔ f r ∈ Q. By mem_basicOpen this proves the required equality. Empty charts, including f a = 0, are vacuous.
- `(hr : r ∈ 𝒜 n)` (theorem): The equality holds for arbitrary r. Retain the current positive-homogeneous proof as an auxiliary, obtained from degreeScaledChartSpec_preimage_basicOpen. At each chart point, its image prime P and ambient prime Q agree under f on positive homogeneous elements; multiplying degree-zero elements by i.2 and using primality extends this to degree zero. Moreover, Ideal.comap f Q is homogeneous: positivity of d and homogeneous decomposition give f (decompose 𝒜 x k) = decompose ℬ (f x) (d*k), by expanding DirectSum.sum_support_decompose and using decompose_of_mem_same/ne. This argument is also implemented in DegreeScaledMapPoint.lean. Ideal.IsHomogeneous.mem_iff therefore yields P = Ideal.comap f Q, proving the conclusion for every r by mem_basicOpen. Zero elements and empty charts require no additional assumptions. Both reported hypotheses can also be removed together.

### [`finiteGroupPresentation_iff_compact_totallyDisconnected`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/FiniteGroupCharacterization.lean#L198-L214) — `formal-frontier-0200`

Snippet: `samples/formal-frontier/formal-frontier-0200.lean`

- `[T2Space G]` (theorem): The existing proof works unchanged without this binder. FiniteGroupPresentation requires only Group and TopologicalSpace; the forward direction transfers compactness and total disconnectedness along its homeomorphism. In the reverse direction, ProfiniteGrp.of requires Group, TopologicalSpace, IsTopologicalGroup, CompactSpace, and TotallyDisconnectedSpace, but not T2Space (Mathlib/Topology/Algebra/Category/ProfiniteGrp/Basic.lean). Hausdorffness follows internally from total disconnectedness for topological groups. No nontriviality assumption is needed, so the trivial group is covered.

### [`SheafCohomology.CompactOpenSections.explicitSectionsComparison_surjective`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/CompactOpenSections.lean#L534-L740) — `formal-frontier-0225`

Snippet: `samples/formal-frontier/formal-frontier-0225.lean`

- `[HasLimitsOfSize.{u, u} C]` (variable): Only preservation of existing sheaf limits is needed, not existence of all limits in C. Mathlib's CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf shows that composing each C-valued sheaf with forget C is a sheaf using the retained limit-preservation assumption alone. Apply TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types to obtain elementwise gluing and uniqueness, replacing the concrete-category gluing/local-equality calls here and in explicitSectionsComparison_injective. All other steps remain unchanged. This also handles empty covers and U = ∅. This hypothesis and instReflectsIsomorphisms can both be deleted.
- `[instReflectsIsomorphisms : (forget C).ReflectsIsomorphisms]` (variable): Reflection is unnecessary because the proof only transfers sheafness from C-valued presheaves to their underlying type-valued presheaves, never conversely. Use CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf, which requires preservation of limits but not reflection, followed by TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types. Replace the gluing/local-equality calls both here and in explicitSectionsComparison_injective accordingly. The remaining steps need no reflection. Unique gluing includes the empty-cover case, so empty U causes no exception. This hypothesis and HasLimitsOfSize can both be deleted.

### [`AlgebraicGeometry.Scheme.Hom.ker_radical_of_isReduced_source`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L154-L160) — `formal-frontier-0232`

Snippet: `samples/formal-frontier/formal-frontier-0232.lean`

- `[QuasiCompact f]` (theorem): By definition, f.ker is the largest ideal sheaf contained componentwise in RingHom.ker (f.app U).hom. Each such ring kernel is radical by Ideal.isRadical_bot.comap, since IsReduced X makes every section ring reduced. Thus f.ideal_ker_le U and Ideal.IsRadical.radical_le_iff show that f.ker.radical is still componentwise contained in these kernels. Scheme.IdealSheafData.le_ofIdeals_iff gives f.ker.radical ≤ f.ker; the reverse inequality is Scheme.IdealSheafData.le_radical. This replaces the quasi-compactness-dependent ker_apply step. The argument also covers trivial section rings and empty schemes; for an empty source the kernel is top, whose radical is top.

### [`AlgebraicGeometry.iInf_ker_eq_vanishingIdeal_iSup_closure_range`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L176-L185) — `formal-frontier-0233`

Snippet: `samples/formal-frontier/formal-frontier-0233.lean`

- `[∀ j, QuasiCompact (f j)]` (theorem): For any morphism g from a reduced scheme, the individual kernel equality holds without quasi-compactness. Put Z = closure(range g) and I = vanishingIdeal Z. The lemma Hom.range_subset_ker_support and closedness of support give Z ≤ g.ker.support; le_support_iff_le_vanishingIdeal then gives g.ker ≤ I. Conversely, every section s ∈ I.ideal U has basic open disjoint from Z, using coe_support_vanishingIdeal, mem_support_iff and mem_zeroLocus_iff. Thus Scheme.preimage_basicOpen shows that the basic open of g.app U s is empty. Reducedness and eq_zero_of_basicOpen_eq_bot imply g.app U s = 0. By Hom.ker's definition and le_ofIdeals_iff, this gives I ≤ g.ker. Apply this equality to each f j and retain the existing vanishingIdeal_iSup argument. Empty sources cause no exception; for empty J, both sides are top by vanishingIdeal_bot.

### [`ContinuousCohomology.coind₁_positive_eq_zero`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/CoinducedAcyclic.lean#L374-L413) — `formal-frontier-0278`

Snippet: `samples/formal-frontier/formal-frontier-0278.lean`

- `[DiscreteTopology X]` (theorem): The statement does not require discreteness to elaborate. Compactness and the topological-group assumptions give LocallyCompactSpace G, without requiring Hausdorffness. Rebuild swapCoind as uncurrying, precomposition by coordinate swap, then currying; rebuild diagonalCoind as uncurrying followed by precomposition by t ↦ (t,t). Their continuity follows from ContinuousMap.continuous_uncurry, continuous_precomp and continuous_curry in Mathlib/Topology/CompactOpen.lean, with no discreteness assumption on the codomain. Thus insertCoind and coind₁Insert can be constructed recursively without the discrete-topology instances. Their pointwise formulas, equivariance and homotopy proofs remain unchanged, and the displayed homology argument then applies unchanged. The lemma π_surjective also has no discreteness assumption. These constructions and identities work for trivial coefficient modules and trivial groups as well; no nontriviality or separation assumption is needed.

### [`MvPowerSeries.existsUnique_firstVariable_division_of_scalar_top`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableDivision.lean#L112-L132) — `formal-frontier-0285`

Snippet: `samples/formal-frontier/formal-frontier-0285.lean`

- `(hprim : Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ => coeff index (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤)` (theorem): Derive hprim from htop and hc. By MvPolynomial.finSuccEquiv_coeff_coeff and coeff_restrictedResidue, the coefficient of f at (0 : Fin n →₀ ℕ).cons d reduces to c. Since c ≠ 0, this coefficient lies outside the maximal ideal and hence is a unit. Its coefficient-content ideal is therefore ⊤ by Ideal.eq_top_of_isUnit_mem. Supply this derived hprim to the existing proof. This works also for n = 0 and d = 0. This deletion retains hc.
- `(hc : c ≠ 0)` (theorem): Derive hc using hprim. The residue is nonzero: otherwise coeff_restrictedResidue puts every coefficient of f in the maximal ideal, contradicting hprim and that ideal's properness. Thus its image under finSuccEquiv is nonzero. Polynomial.coeff_natDegree and Polynomial.leadingCoeff_ne_zero, together with hdegree, show its coefficient at d is nonzero. By htop this is MvPolynomial.C c, so c ≠ 0. Supply this derived hc to the existing proof. Nonzero constant polynomials cover d = 0, and n = 0 causes no exception. This deletion retains hprim; hprim and hc cannot both be deleted.

