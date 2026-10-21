# unnecessary-hypotheses: run `main`, judge `gpt-6.1-sol-high`

| Library | Sampled | Judged | Flagged | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|
| Mathlib | 1000 | 300 | 12 | 4.0% | 2.3%–6.9% | unknown |
| Tau Ceti | 1000 | 300 | 19 | 6.3% | 4.1%–9.7% | unknown |
| Lean Pool | 1000 | 300 | 60 | 20.0% | 15.9%–24.9% | unknown |
| FLT (Anthropic) | 1000 | 300 | 78 | 26.0% | 21.4%–31.2% | unknown |
| Formal Frontier | 1000 | 300 | 18 | 6.0% | 3.8%–9.3% | unknown |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (12 flagged)

### [`RatFunc.Luroth.Φ_natDegree_eq_φ_natDegree`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/RatFunc/Luroth.lean#L182-L185) — `mathlib-0077`

Snippet: `samples/mathlib/mathlib-0077.lean`

- `(h : E ≠ ⊥)` (theorem): The equality holds for any E. Polynomial.natDegree_primPart reduces the left side to (Φ' E).natDegree. IsFractionRing.coeff_integerNormalization_eq_zero_iff shows that Φ' E and (φ E).map (algebraMap E K⟮X⟯) have identical supports, hence identical natDegrees. Polynomial.natDegree_map_eq_of_injective then gives the result. This also handles zero: if φ E = 0, its integer normalization is 0 and primPart_zero makes Φ E = 1; both natDegrees are 0.

### [`Module.Basis.toMatrix_mulVec_repr`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Matrix/Basis.lean#L231-L236) — `mathlib-0083`

Snippet: `samples/mathlib/mathlib-0083.lean`

- `[Finite ι']` (theorem): Only the column index ι needs to be finite for Matrix.mulVec. Without this hypothesis, apply function extensionality at i : ι'; unfolding Matrix.mulVec_apply_eq_sum and Basis.toMatrix_apply gives exactly b'.sum_repr_mul_repr b m i (Mathlib/LinearAlgebra/Basis/Defs.lean). This lemma requires only [Fintype ι], already available, and handles empty indices and trivial semirings as well.

### [`MeasureTheory.projectiveFamilyContent_mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean#L134-L137) — `mathlib-0116`

Snippet: `samples/mathlib/mathlib-0116.lean`

- `(hs : s ∈ measurableCylinders α)` (theorem): Split on whether s belongs to measurableCylinders α. If it does, the existing addContent_mono proof applies. Otherwise, projectiveFamilyContent_eq and the definition of projectiveFamilyFun give projectiveFamilyContent hP s = 0, so the inequality follows from nonnegativity in ℝ≥0∞. This also covers empty or trivial underlying types without additional assumptions.

### [`WeierstrassCurve.preΨ_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean#L314-L318) — `mathlib-0123`

Snippet: `samples/mathlib/mathlib-0123.lean`

- `[Nontrivial R]` (theorem): The remaining hypothesis h already implies Nontrivial R. After deleting this binder, insert `letI : Nontrivial R := nontrivial_of_ne (n : R) 0 h` and use the original proof unchanged. The source lemma constructs nontriviality from two unequal elements; in a trivial ring h is impossible, so that degenerate case is covered.

### [`AdicCompletion.tensor_map_id_left_injective_of_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean#L367-L373) — `mathlib-0139`

Snippet: `samples/mathlib/mathlib-0139.lean`

- `[Module.Finite R M]` (variable): Since R is Noetherian and N is finite, N is Noetherian. Thus `Module.Finite.of_injective f hf` recovers this instance, after which the existing proof applies unchanged. This includes zero modules and trivial rings.
- `[Module.Finite R N]` (variable): Completion of a Noetherian ring is flat, so `Module.Flat.lTensor_preserves_injective_linearMap f hf` proves the conclusion without finiteness of either module. `AlgebraTensorModule.coe_lTensor` identifies its underlying function with the displayed map. To avoid circularity with the subsequent `flat_of_isNoetherian` instance, retain the original finite-case proof as a helper, establish flatness using ideal inclusions exactly as that instance does, then prove the unrestricted result. Both finiteness hypotheses can therefore be removed together; zero modules, trivial rings, and all ideals are covered.

### [`Convex.norm_image_sub_le_of_norm_fderiv_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/MeanValue.lean#L498-L504) — `mathlib-0148`

Snippet: `samples/mathlib/mathlib-0148.lean`

- `[IsRCLikeNormedField 𝕜]` (variable): A metric proof avoids restricting scalars. Set D = ‖y - x‖, γ(t) = x + t • (y - x), and H(t) = ‖f (γ(t)) - f x‖. Convexity keeps γ([0,1]) inside s, and differentiability makes H continuous there. By DifferentiableAt.hasFDerivAt, HasFDerivAt.isLittleO, and IsLittleO.bound, near each z ∈ s we have ‖f w - f z‖ ≤ (C + ε) * ‖w - z‖ for every ε > 0. Thus, when D > 0, the right slopes of H are eventually less than every r > C * D. Apply image_le_of_liminf_slope_right_le_deriv_boundary with boundary B(t) = C * D * t to obtain H(1) ≤ C * D. These lemmas require no IsRCLikeNormedField instance. If D = 0, then x = y and the conclusion is 0 ≤ 0. Empty s is excluded by xs; negative C is excluded by bound x xs. No completeness or real scalar structure on G is needed.

### [`continuous_parametric_integral_of_continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/Bochner/Set.lean#L1121-L1139) — `mathlib-0190`

Snippet: `samples/mathlib/mathlib-0190.lean`

- `[FirstCountableTopology X]` (theorem): Use an epsilon estimate instead of continuousAt_of_dominated. Each section is integrable on s: it is strongly measurable, bounded on the compact set s, and hs.measure_lt_top holds. IsCompact.mem_uniformity_of_prod gives, near any x₀, a uniform bound ‖f x y - f x₀ y‖ < δ for y ∈ s, without countability assumptions on X. Then integral_sub and norm_setIntegral_le_of_norm_le_const bound the integral difference by δ * μ.real s. Choose δ = ε / (μ.real s + 1). This also handles zero measure and empty s; empty X is vacuous. No completeness assumption is needed by these lemmas.
- `[LocallyCompactSpace X]` (theorem): Compact neighborhoods in X can be avoided. IsCompact.mem_uniformity_of_prod, applied to hs and hf.continuousOn with parameter set univ, gives uniform closeness of f x and f x₀ on s near x₀ for arbitrary topological X. The sections are integrable by measurability, compact boundedness, and hs.measure_lt_top. Using integral_sub and norm_setIntegral_le_of_norm_le_const gives an integral difference bounded by δ * μ.real s, proving continuity. Choosing δ = ε / (μ.real s + 1) handles zero measure without division by zero; empty sets and empty X cause no problem. First countability and local compactness can both be deleted together.
- `[SecondCountableTopologyEither Y E]` (theorem): Only the measurability step of the existing proof needs replacement. For each x, the continuous section g := f x is measurable after installing the Borel measurable structure on E, by Continuous.measurable. Its compact image K := g '' s is closed and separable. The measurable predicate g y ∈ K holds for every y ∈ s, so ae_restrict_iff shows it holds almost everywhere under μ.restrict s, even if s is not measurable. Thus aestronglyMeasurable_iff_aemeasurable_separable supplies the required AEStronglyMeasurable g (μ.restrict s), without second countability. The remaining proof is unchanged. For empty s the restricted measure is zero, also covered by this characterization.

### [`CategoryTheory.NormalEpiCategory.mono_of_zero_kernel`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/NormalMono/Equalizers.lean#L299-L313) — `mathlib-0212`

Snippet: `samples/mathlib/mathlib-0212.lean`

- `[HasCokernels C]` (variable): A proof needs only finite coproducts and normal epimorphisms. First, KernelFork.IsLimit.lift' applied to l shows that a ≫ f = 0 implies a = 0. Given u,v : T ⟶ X with u ≫ f = v ≫ f, set p = coprod.desc (𝟙 X) u and q = coprod.desc (𝟙 X) v. Then p ≫ f = q ≫ f. The split epimorphism p is normal by normalEpiOfEpi; write its cokernel witness as w with w ≫ p = 0. Zero cancellation gives w ≫ q = 0, so CokernelCofork.IsColimit.desc' gives h with p ≫ h = q. Precomposing with coprod.inl shows h = 𝟙 X, and precomposing with coprod.inr then gives u = v. No global cokernel existence is used. This argument also covers zero and trivial objects without additional assumptions.

### [`DifferentiableOn.continuousMultilinear_apply_const`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean#L208-L211) — `mathlib-0251`

Snippet: `samples/mathlib/mathlib-0251.lean`

- `[Finite ι]` (variable): ContinuousMultilinearMap.apply 𝕜 M H u is a continuous linear evaluation map without any finiteness assumption (Topology/Algebra/Module/Multilinear/Topology.lean). DifferentiableOn is defined for topological vector spaces, so its statement still elaborates. For each x ∈ s, extract a derivative d from hc x hx and use (apply 𝕜 M H u).comp d as the derivative. Its remainder is evaluation of the original remainder; ContinuousLinearMap.isBigOTVS_comp and IsBigOTVS.trans_isLittleOTVS prove the required little-o estimate. This works for infinite or empty ι and trivial spaces; empty s is vacuous.

### [`ProbabilityTheory.Kernel.withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Kernel/RadonNikodym.lean#L336-L367) — `mathlib-0258`

Snippet: `samples/mathlib/mathlib-0258.lean`

- `(hsm : MeasurableSet s)` (theorem): Let C = (mutuallySingularSetSlice κ η a)ᶜ, which is measurable by measurableSet_mutuallySingularSetSlice. Retain the existing proof as a local claim for every measurable subset of C. Measure.restrict_congr_meas then shows that (withDensity η (rnDeriv κ η) a).restrict C = (κ a).restrict C. Evaluate this equality on the arbitrary set s and apply Measure.restrict_eq_self on both sides using hs. This requires no measurability of s and also covers empty sets and zero measures.

### [`add_tsub_add_le_tsub_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Sub/Defs.lean#L160-L162) — `mathlib-0260`

Snippet: `samples/mathlib/mathlib-0260.lean`

- `[AddLeftMono α]` (variable): It follows from the remaining assumptions. Given h : u ≤ v, add_tsub_le_right gives (u + t) - t ≤ u, hence (u + t) - t ≤ v. Applying tsub_le_iff_right yields u + t ≤ v + t. Commutativity therefore supplies AddLeftMono locally, after which the original proof works unchanged. This argument also covers empty and trivial types; it requires no nonemptiness or cancellation.

### [`MeasureTheory.Measure.prod_smul_left`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Prod.lean#L877-L881) — `mathlib-0275`

Snippet: `samples/mathlib/mathlib-0275.lean`

- `[hν : SFinite ν]` (variable): Split on SFinite ν. In the s-finite case, install the instance and use the existing proof. Otherwise, Measure.prod is defined to be zero for every left measure, so both products vanish. The remaining equality is 0 = c • 0, which follows from the scalar tower: c • 0 = (c • 1) * 0 = 0, also for infinite scalars. This argument also covers empty underlying types.


## Tau Ceti (19 flagged)

### [`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/Basic.lean#L952-L963) — `tauceti-0001`

Snippet: `samples/tauceti/tauceti-0001.lean`

- `(hN : N ≠ 0)` (theorem): Split into N = 0 and N ≠ 0, retaining the existing proof in the latter case. At zero, Nat.primeFactors_zero makes both products equal 1, so it suffices to prove (Gamma0 0).index = 0. By mem_Gamma0_iff_dvd, Gamma0 0 consists of matrices with lower-left entry zero. The matrices L(n) = !![1, 0; n, 1], for n : ℤ, have distinct cosets: QuotientGroup.eq reduces equality to L(m)⁻¹ * L(n) ∈ Gamma0 0, whose lower-left entry is n - m, forcing n = m. Thus the quotient is infinite, and Subgroup.index_eq_zero_iff_infinite gives index zero. Hence the excluded case also satisfies the unchanged conclusion.

### [`RootPairing.coroot'_nonpos_of_mem_negRoots`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/Chamber.lean#L325-L331) — `tauceti-0007`

Snippet: `samples/tauceti/tauceti-0007.lean`

- `[P.IsReduced]` (variable): Recover this from the retained [P.flip.IsReduced]. The perfect pairings P.toLinearMap and P.flip.toLinearMap give reflexivity via Module.IsReflexive.of_isPerfPair, hence torsion-freeness of both modules via Module.IsReflexive.to_isTorsionFree. RootPairing.instFlipIsReduced applied to P.flip then gives P.IsReduced, since P.flip.flip = P definitionally. Install these local instances and use the original proof. This requires no nonempty index or nontrivial module assumption.
- `[P.flip.IsReduced]` (variable): Recover this from the retained [P.IsReduced]. Use Module.IsReflexive.of_isPerfPair on P.toLinearMap and P.flip.toLinearMap, then Module.IsReflexive.to_isTorsionFree to obtain torsion-freeness of both modules. RootPairing.instFlipIsReduced applied to P supplies the deleted instance, after which the original proof works unchanged. Empty index types and trivial modules cause no exception.

### [`TauCeti.cohomologicalDimensionAt_eq_of_isOpen_of_ne_top`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/CohomologicalDimension/OpenSubgroup.lean#L108-L115) — `tauceti-0009`

Snippet: `samples/tauceti/tauceti-0009.lean`

- `[TotallyDisconnectedSpace G]` (variable): For open U, Shapiro's lemma does not require total disconnectedness. The existing Subgroup.exists_continuous_rightCosetFactorization_of_isOpen supplies the continuous factorization used in bijective_explicitShapiroMap1 and coindMap_surjective, without this assumption. Substituting that factorization gives open-subgroup versions of these proofs; coinduction exactness, connecting-map compatibility, and the AllDegrees.lean induction then give Shapiro in every degree. Using this open-subgroup version, both the closed-subgroup inequality (specialized to open U) and the finite-dimension descent proof work unchanged. Compactness still supplies compactness of U, finite index, and preservation of primary torsion. This argument works for arbitrary p, including 0 and 1, and for the trivial group; groups cannot be empty.

### [`HeckeRing.GLn.posDetInt_le_commensurator`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/HeckeRing/GLn/Basic.lean#L712-L717) — `tauceti-0020`

Snippet: `samples/tauceti/tauceti-0020.lean`

- `[NeZero n]` (variable): Neither posDetInt nor SLnZ requires this instance. Split on n = 0. For n ≠ 0, install NeZero n and use the existing proof with mem_commensurator_of_hasIntEntries. For n = 0, every g : GL (Fin 0) ℚ equals 1: apply Units.ext and matrix extensionality, eliminating the row index with Fin.elim0. Thus membership in the commensurator's submonoid follows from one_mem, regardless of hg.

### [`TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Data/Nat/Factorization/GcdSplit.lean#L56-L71) — `tauceti-0078`

Snippet: `samples/tauceti/tauceti-0078.lean`

- `(hp : p.Prime)` (theorem): Split on whether p is prime. In the prime case, use the existing proof. Otherwise, Nat.ordCompl_of_not_prime gives ordCompl[p] m = m and ordCompl[p] n = n, while Nat.factorization_eq_zero_of_not_prime makes both exponents zero. The conclusion reduces to gcd m n = gcd m n * 1. This also covers p = 0 and p = 1, since p ^ 0 = 1.

### [`TauCeti.DynkinType.geckGroupScheme_hom_ext`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/GeckLattice/GroupScheme.lean#L331-L352) — `tauceti-0084`

Snippet: `samples/tauceti/tauceti-0084.lean`

- `(htorus : t.geckWeightTorus ht ≫ φ = t.geckWeightTorus ht ≫ ψ)` (theorem): Agreement on root subgroups already implies agreement on the torus. The source lemma kostantCoordinateCocharacter_torusCharacter_mem_kostantElementarySubgroup, applied to a torus point supported at i with value u, puts the i-th coordinate-cocharacter at u² in the elementary subgroup: rootGeneratorWeight_inl and cartanMatrix_apply_same give exponent 2, and isSl2Triple_geckRepresentation supplies the triple. Taking products, every represented coordinatewise-square torus point is elementary. Thus hroot gives agreement after precomposing the torus restrictions with the squaring morphism. Its coordinate map on ℤ[Fin t.rank →₀ ℤ] sends each monomial indexed by m to that indexed by 2m and is injective, since doubling integer exponent vectors is injective. Cancel this map on coordinate morphisms to obtain htorus, then use the original proof. This does not assume units have square roots or Cartan rows are primitive; the argument also covers rank one, characteristic-two points, and an empty index set.

### [`TauCeti.RoughForm.inChartAt_mpullback`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Geometry/Manifold/DifferentialForm/Pullback/Chart.lean#L37-L53) — `tauceti-0108`

Snippet: `samples/tauceti/tauceti-0108.lean`

- `(hf : MDifferentiableAt I I' f ((extChartAt I α).symm z))` (theorem): Split on hf; the positive case uses the existing proof. Otherwise put c = extChartAt I α and x = c.symm z. The composite f ∘ c.symm cannot be MDifferentiableWithinAt on range I at z: composing with c using MDifferentiableWithinAt.comp_of_eq and mdifferentiableAt_extChartAt would make f differentiable within c.source at x, by c.left_inv. Since c.source is a neighborhood of x, MDifferentiableWithinAt.mdifferentiableAt would contradict ¬hf. Thus mfderiv_zero_of_not_mdifferentiableAt and mfderivWithin_zero_of_not_mdifferentiableWithinAt make both relevant derivatives zero. After inChartAt_apply and mpullback_apply, both sides evaluate the same form on the same zero tuple. This also handles k = 0 (the tuple is empty, without claiming the form vanishes), trivial spaces, and boundary points because differentiation remains within range I.

### [`LipschitzWith.ae_finite_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Function/AreaFormula/Real.lean#L119-L126) — `tauceti-0115`

Snippet: `samples/tauceti/tauceti-0115.lean`

- `(hs : NullMeasurableSet s volume)` (theorem): Write J x = (fderiv ℝ f x).normDet and r = s ∩ {x | J x ≠ 0}. By IntegrableOn.mono_set, J is integrable on r. IntegrableOn.restrict_toMeasurable then shows that it remains integrable on the measurable hull t = toMeasurable volume r. Apply ae_summable_fiber on t with constant weight 1 and the existing finite-fiber argument. Meanwhile, hf.euclideanHausdorffMeasure_image_setOf_normDet_fderiv_eq_zero says that f '' {x | J x = 0} is null. Outside this image, every point of the fiber in s belongs to r, hence to t, so that fiber is finite. This argument also covers empty sets and zero-dimensional spaces without extra assumptions.

### [`TauCeti.exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Cohomology.lean#L195-L206) — `tauceti-0118`

Snippet: `samples/tauceti/tauceti-0118.lean`

- `[FiniteDimensional K L]` (variable): FiniteDimensional abbreviates Module.Finite. The remaining hypotheses imply it by Module.Finite.of_restrictScalars_finite ℚ_[p] K L. Install this as a local instance and reuse the existing proof. The lemma has no nonzero-dimension exception.
- `[CharZero L]` (variable): The remaining Algebra ℚ_[p] L gives an injective algebra map between fields, and ℚ_[p] has characteristic zero. Thus charZero_of_injective_algebraMap reconstructs CharZero L locally, after which the existing proof applies. Fields exclude the trivial-target exception.
- `[CharZero K]` (variable): Similarly, Algebra ℚ_[p] K and injectivity of the algebra map between fields give CharZero K by charZero_of_injective_algebraMap. Install it locally and reuse the proof. There is no trivial-field exception; both characteristic-zero hypotheses can also be deleted together.

### [`TauCeti.ContCohomology.explicitFiniteQuotientSystem2_obj`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/FiniteQuotient/Explicit.lean#L396-L402) — `tauceti-0131`

Snippet: `samples/tauceti/tauceti-0131.lean`

- `[IsTopologicalAddGroup M]` (variable): The remaining [DiscreteTopology M] implies this instance via Mathlib's isTopologicalAddGroup_of_discreteTopology. With `omit [IsTopologicalAddGroup M] in`, the statement still elaborates and the proof remains `by rfl`. This applies equally to trivial coefficient groups; no additional nonemptiness or nontriviality assumption is needed.

### [`Matrix.ProjectiveSpecialLinearGroup.isParabolic_inv_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup/FinTwo.lean#L103-L117) — `tauceti-0134`

Snippet: `samples/tauceti/tauceti-0134.lean`

- `[NoZeroDivisors R]` (variable): IsParabolic is defined existentially using a parabolic SL representative, without this assumption. First prove that an SL(2,R) matrix is parabolic iff its inverse is: the existing hscalar calculation and subsequent simplification work over any commutative ring, using SpecialLinearGroup.coe_inv and Matrix.adjugate_fin_two. Then map each existential witness a to a⁻¹, using QuotientGroup.mk_inv and inverse involutivity. This avoids isParabolic_mk_iff, the step requiring NoZeroDivisors. The calculation uses no cancellation and works with zero divisors and in characteristic two; in the trivial ring all matrices are scalar, so both sides are false.

### [`TauCeti.IsFiniteType.exists_chain_of_reachable`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/FiniteType/Diagram.lean#L154-L185) — `tauceti-0149`

Snippet: `samples/tauceti/tauceti-0149.lean`

- `(h : IsFiniteType A)` (theorem): The conclusion holds for every integer matrix. Reachable means a nonempty type of walks; using Walk.getVert and diagramGraph_adj gives a finite sequence with the required endpoints and consecutive nonzero entries. Choose such a sequence of minimum length using Nat.find, without requiring its steps to remain diagram edges. Repeated vertices would allow deleting a loop, contradicting minimality, so the sequence is injective on its index interval. Any nonzero A (w i) (w j) with i + 1 < j ≤ n would allow replacing that segment by one step, again contradicting minimality. Thus all required forward nonconsecutive entries vanish, even for asymmetric matrices. When u = v, length zero and the constant sequence suffice; an empty B cannot supply the endpoints. No finite-type assumption is needed.

### [`TauCeti.rightTrace_biprod`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/CategoryTheory/Monoidal/Pivotal/Biproduct.lean#L114-L125) — `tauceti-0163`

Snippet: `samples/tauceti/tauceti-0163.lean`

- `[MonoidalPreadditive C]` (variable): Put B = X ⊞ Y, D = Bᘁ and F = tensorRight D. Rigidity supplies tensorRightAdjunction D Dᘁ, so F preserves coproducts and zero morphisms (preservesZeroMorphisms_of_isLeftAdjoint). By preservesBinaryBiproduct_of_preservesBinaryCoproduct, isBinaryBilimitOfPreserves and IsBilimit.binary_total, the mapped biproduct satisfies F.map fst ≫ F.map inl + F.map snd ≫ F.map inr = 𝟙 (F.obj B). Insert this identity before F.map f in rightTrace_def. Distributivity of composition from Preadditive C and functoriality split the trace into rightTrace (fst ≫ inl ≫ f) + rightTrace (snd ≫ inr ≫ f), without using rightTrace_add or additive whiskering. Apply rightTrace_comm, which requires no MonoidalPreadditive instance, to obtain the conclusion. This argument uses only the specified biproduct and also covers zero objects, zero morphisms and trivial categories.

### [`MeasureTheory.Measure.rnDeriv_mul_measure_singleton`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Measure/Decomposition/Lebesgue.lean#L46-L58) — `tauceti-0170`

Snippet: `samples/tauceti/tauceti-0170.lean`

- `[MeasurableSingletonClass α]` (variable): Set f := μ.rnDeriv ν, which is measurable by measurable_rnDeriv. The fiber S := {y | f y = f x} is measurable and contains x. Using restrict_withDensity, withDensity_congr_ae, and withDensity_const gives (ν.withDensity f).restrict S = f x • ν.restrict S. Evaluate at {x} and use restrict_apply' and smul_apply to obtain ν.withDensity f {x} = f x * ν {x}, without requiring {x} measurable. The original argument showing the singular part vanishes uses no measurable-singleton assumption; combine it with this identity and haveLebesgueDecomposition_add. These lemmas allow zero or infinite density and infinite singleton mass, so no exceptional cases require the deleted assumption.

### [`TauCeti.exists_coprimePart_indK0_of_trivial_eq_nsmul`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Permutation/PrimePower.lean#L131-L148) — `tauceti-0194`

Snippet: `samples/tauceti/tauceti-0194.lean`

- `[Fact p.Prime]` (variable): CharP.char_is_prime_or_zero k p gives p.Prime ∨ p = 0. In the prime case, install Fact p.Prime and use the existing proof. For p = 0, choose D = C: its finite, nonempty underlying group has positive cardinality, so ¬ 0 ∣ Nat.card C. Subgroup.relIndex_self and Nat.factorization_zero_right give the index equality, since 0 ^ 0 = 1; the Grothendieck-group equality reduces to x = 1 • x. This also covers trivial C.

### [`TauCeti.IsGradedExtInternallyFinite.shiftSourceInverse`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Homology/EulerCharacteristic/ExtEuler/Graded/Shift.lean#L304-L308) — `tauceti-0229`

Snippet: `samples/tauceti/tauceti-0229.lean`

- `[e.functor.Additive]` (variable): An equivalence of abelian categories is automatically additive: it preserves limits (isEquivalencePreservesLimits), hence binary products and terminal objects, and therefore zero morphisms (preservesZeroMorphisms_of_preserves_terminal_object). Apply Functor.additive_of_preserves_binary_products to obtain a local Additive instance, then use the existing proof unchanged. Neither Functor.Linear nor the conclusion requires this binder to elaborate. This argument also applies to trivial abelian categories.

### [`TauCeti.cwEulerChar_preimage_of_card_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/Covering.lean#L75-L88) — `tauceti-0231`

Snippet: `samples/tauceti/tauceti-0231.lean`

- `(hfin : ∀ b, Finite ↥(p ⁻¹' {b}))` (variable): Replace the cell-counting step using cellPreimageEquiv. If d ≠ 0, hd and Nat.finite_of_card_ne_zero give finite fibres over every cell centre, so Nat.card_sigma proves the count. If d = 0, the lifted cell type has Nat.card zero: if infinite this is Nat.card_eq_zero_of_infinite; if finite, each fibre injects into it, hence is finite and empty by hd and Finite.card_eq_zero_iff. The remaining finite-range proof is unchanged. Empty complexes and empty fibres are covered.
- `[RelCWComplex.Finite C]` (variable): Retaining hfin, hd and Finite.equivFinOfCardEq identify every fibre over a cell centre with Fin d. Thus cellPreimageEquiv identifies lifted n-cells with cell C n × Fin d. Nat.card_prod gives the required cell count without any finiteness assumption on cell C n. Expand cwEulerChar_def and apply mul_finsum over ℤ instead of truncating to a finite range. This works for infinite-dimensional complexes, infinite cell types, d = 0, and empty complexes.

### [`TauCeti.schwarzChristoffelEdgeAngle_comp_strictMono`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/GlobalTurning.lean#L114-L125) — `tauceti-0238`

Snippet: `samples/tauceti/tauceti-0238.lean`

- `[LocallyFiniteOrder ι]` (variable): The statement does not use this instance: schwarzChristoffelEdgeAngle requires only Fintype. Omit the hypothesis and begin the proof with `letI : LocallyFiniteOrder ι := Fintype.toLocallyFiniteOrder`, the constructor in Mathlib/Order/Interval/Finset/Defs.lean. The existing proof then works unchanged. This constructor also works for empty and singleton types, where StrictMono is vacuous.

### [`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isCompact`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/PDE/Regularity/HolderContinuity.lean#L238-L258) — `tauceti-0281`

Snippet: `samples/tauceti/tauceti-0281.lean`

- `[Nonempty ι]` (theorem): Split into nonempty and empty cases for ι. In the nonempty case, use the existing proof via the drift theorem. If ι is empty, EuclideanSpace ℝ ι is subsingleton: PiLp.ext proves any two points equal by eliminating their coordinate index. Thus every K is subsingleton, and Set.Subsingleton.holderOnWith gives the conclusion with α = 1 and C = 0 for any precise representative. This also covers empty K and requires none of the PDE assumptions in that branch.


## Lean Pool (60 flagged)

### [`ViscositySolns.exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Aleksandrov/JetCalculus/Strictification/StrictifiedObjective.lean#L337-L370) — `lean-pool-0000`

Snippet: `samples/lean-pool/lean-pool-0000.lean`

- `(hr : 0 <= r)` (theorem): Split into 0 ≤ r and r < 0. In the first case, use the existing proof, including r = 0. In the second case, Metric.closedBall_eq_empty.mpr makes the ball empty; choose lambda = 0. By its definition, CoordinateSemiconvexOn is vacuous on the empty set because it requires x ∈ C. This also works when n = 0.

### [`NavierStokes.ParticularWaveBounds.pressure_class`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ParticularWaveBounds.lean#L1371-L1389) — `lean-pool-0009`

Snippet: `samples/lean-pool/lean-pool-0009.lean`

- `(hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)` (theorem): The inverse-normal estimate does not require an upper bound. By PolynomialJets.norm_sq, q(n,x) = ‖N n x‖² has polynomial jets, and hb with hlower gives q ≥ b² > 0. Mathlib's iter_deriv_inv, iteratedDeriv_eq_iterate and norm_iteratedFDeriv_eq_norm_iteratedDeriv bound the kth derivative of inversion at q by k! * (b²)^(-(k+1)). For each finite derivative order these are uniform constants. Applying norm_iteratedFDerivWithin_comp_le, as in PolynomialJets.compact_comp, therefore proves polynomial jets for q⁻¹ without compactness or hupper. Convert these using polynomialJets_unweighted and retain the numerator, multiplication and band_smul steps of the existing proof. Empty domains cause no problem; zero normals are excluded on the domain by hb and hlower. Zero frequencies also cause no problem: division is zero there, and the existing band_smul argument already handles them.

### [`CKN.Leray.integral_ae_eq_integral_jointRep`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegularisedJointRep.lean#L247-L298) — `lean-pool-0024`

Snippet: `samples/lean-pool/lean-pool-0024.lean`

- `[CompleteSpace E]` (variable): With finite dimensionality retained, `FiniteDimensional.complete ℂ E` supplies this instance. Omit the variable and introduce that instance locally; the existing proof then applies unchanged. This also covers zero-dimensional E.
- `[FiniteDimensional ℂ E]` (variable): With completeness retained, the proof through `hkey` needs no finite dimensionality. Apply `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` directly to I and H, using `hIint` and `hHint`. Their vector-valued set integrals agree by `ext_inner_left ℂ`: rewriting with `integral_inner` reduces each scalar equality to `hkey`. This replaces the finite-basis argument and works even for nonseparable complete E, trivial E, empty domains, and zero measures.

### [`IsoGraph.Canon.splitCell_tr_general`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Equivariance.lean#L3331-L3342) — `lean-pool-0028`

Snippet: `samples/lean-pool/lean-pool-0028.lean`

- `(hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))` (theorem): The trace does not depend on the scatter or write outputs. Destructure the actual scatterFrom result and its subsequent writeFrom result, then apply splitCell_eq_general with their defining equalities and hb, h1, h2, ho, hbd. Projecting .tr proves the conclusion without hsc or the original hw. These total functions also handle empty arrays and zero fuel, so no additional assumptions are needed. Both hsc and hw can be deleted together.
- `(hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))` (theorem): Destructure the actual writeFrom block c block.size 0 st.lab st.pos result into fresh lab' and pos'. Apply splitCell_eq_general using its defining equality instead of hw, then project .tr. The trace is supplied by hbd independently of the write outputs, including for empty blocks. This hypothesis can also be deleted together with hsc.

### [`ESS.buCut_gradient_absorption`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUShortGradient.lean#L28-L102) — `lean-pool-0033`

Snippet: `samples/lean-pool/lean-pool-0033.lean`

- `(hκ : 0 ≤ buCutScalar κ z)` (theorem): Split on whether buCutScalar κ z ≥ 0. In that case use the existing proof. Otherwise the left side is nonpositive by Real.sqrt_nonneg, while the right side is nonnegative by hM and vec3EuclideanNorm_nonneg. Zero cutoff and zero gradients are covered.
- `(hM : 0 ≤ M)` (theorem): Recover it from hderiv at (0 : Fin 3): 0 ≤ |spatialPartial (buCutScalar κ) 0 z| ≤ M. Then the existing proof applies unchanged. Fin 3 is nonempty, and this also covers zero derivatives and M = 0.

### [`IsoGraph.Canon.individualize_refines`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Progress.lean#L192-L202) — `lean-pool-0038`

Snippet: `samples/lean-pool/lean-pool-0038.lean`

- `(hv : v < n)` (theorem): If n = 0, Refines is vacuous. Otherwise split on v < n, using the existing proof in the valid case. When v ≥ n, hp.posSize and getElem!_neg give p.pos[v]! = 0. Set w := p.lab[0]!. Then hp.labLt gives w < n and hp.posLab gives p.pos[w]! = 0. By individualize_cst_eq, individualizing v and w produces identical cst arrays, since these depend on the vertex only through its position. Thus the existing valid-vertex argument for w proves the result for v.

### [`TauCeti.DavisKahanExt.le_riccati_small_root_of_quadratic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Riccati/BoundedSharpEstimates.lean#L41-L89) — `lean-pool-0045`

Snippet: `samples/lean-pool/lean-pool-0045.lean`

- `(hb : 0 ≤ b)` (theorem): Split on 0 ≤ b; the existing proof handles that branch, including b = 0. If b < 0, put f = b*(1+t²)-d*t ≥ 0 and Δ = d²-4*b². The identity Δ-(2*b*t-d)² = -4*b*f gives (2*b*t-d)² ≤ Δ, hence Δ ≥ 0. With s = √Δ, Real.sqrt_nonneg and Real.sq_sqrt imply 2*b*t ≥ d-s. Multiplying by d+s > 0 gives 2*b*t*(d+s) ≥ 4*b². Since 2*b < 0, this yields t*(d+s) ≤ 2*b, which is the conclusion by le_div_iff₀. This also covers Δ = 0.
- `(hd : 0 < d)` (theorem): It follows from hb and hsmall: 0 ≤ 2*b < d. Recover hd with linarith and retain the existing proof. This and hsmall cannot both be deleted: b = d = 0 and t = 1/2 satisfy the remaining assumptions but violate the conclusion.
- `(hsmall : 2 * b < d)` (theorem): Split on 2*b < d and use the existing proof in that case. Otherwise d ≤ 2*b, and hb and hd imply d²-4*b² ≤ 0. Real.sqrt_eq_zero_of_nonpos makes the conclusion's right-hand side 2*b/d ≥ 1, so ht1 suffices. This includes the zero-discriminant case. This and hd cannot both be deleted, as shown by b = d = 0 and t = 1/2.

### [`NavierStokes.HeatedOutgoing.E_times_U`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/HeatedOutgoing.lean#L1197-L1206) — `lean-pool-0047`

Snippet: `samples/lean-pool/lean-pool-0047.lean`

- `(hXR : 0 < XR)` (theorem): Keep hX and split on the sign of XR. For XR > 0, use the existing proof. For XR < 0, the definitions and Real.log_neg_eq_log show that heatE, U, and OutgoingDilation.E are unchanged when XR is replaced by -XR; apply heatE_times_U at -XR. Meanwhile patchRadius F XR < 0, so X / patchRadius F XR < 0 and correction_zero_outside makes patchIncrement zero, since compensationPatch.left = 1. For XR = 0, both radii are zero: division by zero and Real.log_zero make the switch zero by OutgoingSchedule.sigma_zero, and correction_zero_outside makes the correction at zero vanish. Thus E equals OutgoingDilation.E in this case.
- `(hX : 0 < X)` (theorem): Keep hXR. The proof of patchIncrement * U = 0 already works for every X, since correction_times_U_zero has no positivity assumption on X. Extend the heatE step as follows. At X = 0, Real.log_zero and OutgoingSchedule.sigma_zero make the switch zero, so heatE equals OutgoingDilation.E. For X < 0, put Y = -X > 0. By the definitions and Real.log_neg_eq_log, U at X equals U at Y, and the heat switch at X equals that at Y. If Y ≤ switchRadius F XR, HeatTailEdit.switch_zero makes heatE unchanged at X. Otherwise U_after_switch makes U at Y, hence at X, zero. The original argument handles X > 0.

### [`RS.tensorPow_id_ne_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/SuperEmbed/Standard.lean#L336-L359) — `lean-pool-0048`

Snippet: `samples/lean-pool/lean-pool-0048.lean`

- `[MonoidalPreadditive A]` (theorem): Let F = tensorRight U. The isomorphisms α_ X U U ≪≫ whiskerLeftIso X hUU ≪≫ ρ_ X form a natural isomorphism F ⋙ F ≅ 𝟭 A. Thus Equivalence.mk makes F an equivalence with itself as inverse, so F is full. Mathlib's Functor.preservesZeroMorphisms_of_full then gives F.map_zero without MonoidalPreadditive. Replace the proof's use of MonoidalPreadditive.zero_whiskerRight with this fact; the remaining induction is unchanged. This requires no zero object or nonemptiness assumption; the unit supplies an object, and hone already excludes its being zero.

### [`OS4Ergodicity.OS4''_implies_OS4_Ergodicity`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OSforGFF/OS/OS4Ergodicity.lean#L1196-L1200) — `lean-pool-0073`

Snippet: `samples/lean-pool/lean-pool-0073.lean`

- `os4DoublePrimeClustering m →` (theorem): This anonymous premise can be deleted. In OS/OS4Clustering.lean, QFT.gaussianFreeField_satisfies_OS4_PolynomialClustering proves polynomial clustering for every positive mass and every positive exponent. Import that file and specialize the lemma to m, 6, and (by norm_num); its conclusion is definitionally os4DoublePrimeClustering m. Pass this proof to OS4''_implies_OS4', then apply OS4'_implies_OS4 as before. The retained [Fact (0 < m)] excludes zero and negative masses, and the existing chain covers all cases of the ergodicity conclusion.

### [`EulerOrdinarySobolev.Evolution.gradient_logarithmic_envelope`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/OrdinaryEulerBKM.lean#L109-L141) — `lean-pool-0078`

Snippet: `samples/lean-pool/lean-pool-0078.lean`

- `(hC : 0 ≤ C)` (variable): Derive hC from hW and hlog at the supplied t. By tensorNorm_nonneg, Real.log_le_log and Real.log_exp, log (exp 1 + tensorNorm 3 (U.velocity t)) ≥ 1. Thus hW t and norm nonnegativity make B = 1 + ‖(U.velocity t).toLp‖ + W t * log (...) strictly positive. Meanwhile, U.gradientNormPath_nonneg t and hlog t give 0 ≤ C * B. The lemma nonneg_of_mul_nonneg_left yields 0 ≤ C, after which the original proof applies unchanged. This also covers C = 0, zero velocity and T = 0; the supplied t ensures an evaluation point exists.

### [`MaxAddDegree.represents_zero_of_degree_lt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConwayRefinement/ConwayRefinement/Algebra/Valuation/DegreeRepresentatives.lean#L140-L143) — `lean-pool-0082`

Snippet: `samples/lean-pool/lean-pool-0082.lean`

- `[IsOrderedCancelAddMonoid M]` (variable): Represents, homogeneousMk, and the additive associated graded construction do not require this instance. After omitting it, use h.le for degree_le, unfold homogeneousMk, rewrite the component class to zero using componentMk_eq_zero_iff (explicitly proved without this instance), and finish with (DirectSum.of ν.Component m).map_zero. This argument also covers zero representatives and trivial rings or degree monoids.

### [`NavierStokes.SignedCopyBounds.local_mul`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SignedCopyBounds.lean#L91-L97) — `lean-pool-0090`

Snippet: `samples/lean-pool/lean-pool-0090.lean`

- `(hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)` (theorem): Reproduce the proof of LocalJets.bilinear, replacing its use of hw by nonnegativity of the majorant obtained from hf.bounds at j = 0: 0 ≤ ‖iteratedFDeriv ℝ 0 (f n i) x‖ ≤ majorant s w α A p n x. The remaining bilinear estimate and majorant_mul identity are unchanged. Empty domains or cells are vacuous, and zero majorants cause no problem. Both hw and hv can be deleted together.
- `(hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x)` (theorem): In the proof of LocalJets.bilinear, hg.bounds at j = 0 already implies that its majorant is nonnegative at every point where a bound is required. This replaces the sole use of hv; smoothness and majorant_mul need no weight-sign assumptions. The argument also covers zero majorants and empty domains or cells. Both hv and hw can be deleted together.

### [`RS.kernelSubobject_tensorHom_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/KernelPow.lean#L729-L761) — `lean-pool-0091`

Snippet: `samples/lean-pool/lean-pool-0091.lean`

- `[MonoidalPreadditive A]` (theorem): This follows from rigidity and abelianness. TensorExact.lean supplies limit-preservation instances for tensorLeft and tensorRight. They therefore preserve terminal objects and zero morphisms; Functor.additive_of_preserves_binary_products makes both functors additive. Their map_zero and map_add properties supply all four fields of MonoidalPreadditive. Install this derived instance and retain the displayed proof. This also works for zero objects and trivial categories.
- `[Epi p₁]` (theorem): Factor p₁ = e ≫ m through its image, with e epi and m mono. Rigidity makes tensorRight W₂ preserve monomorphisms, so p₁ ⊗ₘ p₂ = (e ⊗ₘ p₂) ≫ (m ▷ W₂) has the same kernel subobject as e ⊗ₘ p₂, by kernelSubobject_comp_mono. Apply the displayed epi-case argument to e and p₂. The kernel arrow of e factors through the kernel arrow of p₁; right whiskering this factorization gives the required comparison of their image subobjects. The other summand is unchanged. Image factorization and these comparisons remain valid for zero morphisms and zero objects.

### [`Egrs75.ClearingP3.lowDigits_half_pred_pow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Egrs75/SubtractBranch.lean#L172-L181) — `lean-pool-0093`

Snippet: `samples/lean-pool/lean-pool-0093.lean`

- `(hp : 3 ≤ p)` (theorem): Odd p gives p = 2*k + 1, so either p = 1 or 3 ≤ p. In the latter case the existing induction works unchanged. When p = 1, (p^m - 1)/2 = 0 for every m by one_pow, and RoundUp.lowDigits_zero 1 proves the conclusion. Thus the only additional odd-base case also holds.

### [`NFChoice.Compiler.NFCompactLeafFinalGate.axSiCompact`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NFWeakPartition/NFCompactLeafFinalGate.lean#L209-L255) — `lean-pool-0096`

Snippet: `samples/lean-pool/lean-pool-0096.lean`

- `(hxy : x ≠ y)` (theorem): Split on x = y; the unequal case uses the existing proof. When x = y, choose an empty object E for the existential witness. Both class-membership atoms are false by the definitions of Wff.Holds and Class.Holds, since their target is E; the remaining inequalities prevent its binding from being overwritten. Such E follows from literalAxNin, available through realizes_literal_axiom hNF .axNin: starting with A, form its complement B, then U = NAND(A,B), then E = NAND(U,U). A valuation supplies A; if S is empty, validity is vacuous.
- `(hzw : z ≠ w)` (theorem): Keep the same witness Y, but after defining v', specialize hY at A = v' z and B = v' w instead of Z and W. Use xs = [B,A,Y,v x]. The z and w lookup equalities are then definitional; the y and x equalities follow from the remaining inequalities. The same holds_literalSingletonPairMem and holds_literalPairMem lemmas finish, and neither requires distinct variable names. This also covers z = w, where A = B because the inner update overwrites the outer one. Empty carriers make validity vacuous.

### [`NavierStokes.TerminalCompensation.physicalProfile_family_contDiffOn`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalCompensation.lean#L1082-L1099) — `lean-pool-0105`

Snippet: `samples/lean-pool/lean-pool-0105.lean`

- `(hR : 0 < R)` (theorem): Only the proof of hb needs changing. Split on R = 0. If R = 0, division by zero makes the base term constant, baseProfile lam 0, so contDiffOn_const applies regardless of its value. Otherwise, div_ne_zero hz.2.ne' hR0 gives z.2 / R ≠ 0, and Real.contDiffAt_rpow_const_of_ne proves hb exactly as before, including for negative R. The amplitude and correction arguments remain unchanged.

### [`NavierStokes.PolarCharts.chart_finiteJets_uniform`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalGraphBounds.lean#L336-L354) — `lean-pool-0108`

Snippet: `samples/lean-pool/lean-pool-0108.lean`

- `(ha : 0 < a)` (theorem): The charts are smooth for every real a. From the definition, positiveRadius (-ℓ) (-x) = -positiveRadius ℓ x; thus positiveRadius_pos implies that positiveRadius ℓ x is strictly negative when ℓ < 0. For a < 0, the denominator in extendedBase is therefore nonzero, while its square-root argument is positive since a²/32 > 0. The existing smoothness proof works using these facts and ContDiff.div and ContDiff.sqrt. For a = 0, positiveRadius 0 x = 0 by Real.smoothTransition.zero and division by zero, so chart 0 j is the constant (0, offset j), hence smooth. With this unconditional chart smoothness result, the original compactness and finite-sum proof applies unchanged, including empty closed balls and m = 0.

### [`NavierStokes.SlowStressSupport.axial_stress_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SlowStressSupport.lean#L2093-L2133) — `lean-pool-0111`

Snippet: `samples/lean-pool/lean-pool-0111.lean`

- `(hn : 0 < n)` (theorem): Its only use is proving n - 1 ≤ n. Replace that proof with Nat.sub_le n 1; everything else is unchanged. This includes n = 0, where truncated subtraction gives n - 1 = 0.
- `(hB : 0 ≤ B)` (theorem): Split on 0 ≤ B, retaining the existing proof in that case. If B < 0, the existing construction of hout is still valid and makes axialDensity zero at every nonnegative radius. By the definition of stress and its primitive integral, axialStress is therefore zero at positive radii, and it is zero by definition at nonpositive radii. Thus radialSupport holds even though Icc a B is empty. The existing smoothness and derivative proofs do not use hB.
- `(hV : ∀ j, j ≤ n → exterior B S (v j))` (theorem): From the definition conv n v u = ∑ i ∈ range (n + 1), v i * u (n - i), hU already proves exterior B S (conv n v u): each second factor vanishes since n - i ≤ n. Inline axial_integral_zero and axial_integral_balance, replacing their use of exterior_conv_left hV by this fact. Likewise inline exterior_axialDensity and use this fact in its exterior_dr step. These are the only uses of hV; all remaining steps are unchanged. The argument works for every radius and for empty S as well.

### [`NumberField.Odlyzko.summable_integral_norm_idealSet_complexPlaceMellinGaussian`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/CompletedZeta/ConeGaussianInterchange.lean#L96-L112) — `lean-pool-0115`

Snippet: `samples/lean-pool/lean-pool-0115.lean`

- `[IsTotallyComplex K]` (variable): This instance is not needed by the statement. A comparison argument replaces the totally complex integral formula. Put σ = s.re, d = [K:ℚ], m = #InfinitePlace K, x = idealSetElement K J a and N = idealSetIntNorm K J a ≥ 1. By the definitions of fundamentalCone and logMap and ZSpan.fundamentalDomain_isBounded, log(w x) − log(N)/d is uniformly bounded for every place except the distinguished one. InfinitePlace.prod_eq_abs_norm and sum_mult_eq give the same bound at that remaining place. Consequently P = ∏ w, (w x)^2 ≥ c N^(2m/d) ≥ c N for some c > 0 independent of a: multiplicities are 1 or 2, so d ≤ 2m. The instance-free lemmas norm_complexPlaceMellinGaussian and integral_totallyComplexGaussian_eq_prod express the integral as C P^(−σ), hence bound it by C c^(−σ) N^(−σ). Apply Summable.of_norm_bounded to the norm of summable_idealSet_inverseNormPower, which also needs no totally complex instance. All x are nonzero and N ≥ 1 by idealSetElement_ne_zero and idealSetIntNorm_ne_zero, so no zero/junk-value case arises. Number fields have positive degree and nonempty infinite places; the argument also covers unit rank zero.

### [`CKN.Leray.mildShiftedStokesIntegral_continuous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierMildIntegral.lean#L216-L225) — `lean-pool-0117`

Snippet: `samples/lean-pool/lean-pool-0117.lean`

- `(hFC : ∀ t, ‖F t‖ ≤ C)` (theorem): Continuity of F supplies the local bound needed by dominated convergence. At each t₀, IsCompact.exists_bound_of_continuousOn bounds ‖F‖ on [t₀ - 1 - T, t₀ + 1]; enlarge this bound to a nonnegative D. For |t - t₀| < 1 and 0 < τ ≤ T, this bounds ‖F (t - τ)‖. Repeat the existing continuousAt proof with D replacing C and this neighborhood bound replacing hFC: intervalIntegral.continuousAt_of_dominated_interval requires domination only eventually near t₀. The existing integrable Abel kernel and almost-everywhere continuity arguments remain unchanged. T = 0 gives a zero integral.
- `(hC : 0 ≤ C)` (theorem): It follows from hFC at time zero: (norm_nonneg (F 0)).trans (hFC 0). Supply this proof to mildShiftedStokesIntegral_continuousAt instead of hC. This also covers C = 0.
- `(hT : 0 ≤ T)` (theorem): Split on 0 ≤ T. The nonnegative case uses the existing proof. Otherwise T < 0, and every τ in the unordered interval between 0 and T satisfies τ ≤ 0. By its definition, mildShiftedStokesIntegrand is therefore zero throughout that interval, for every t. intervalIntegral.integral_congr and intervalIntegral.integral_zero make the integral identically zero, hence continuous. T = 0 is already covered.

### [`ESS.buGaussian_shifted_trace_strip_tendsto`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUGaussianAverageTools.lean#L334-L436) — `lean-pool-0118`

Snippet: `samples/lean-pool/lean-pool-0118.lean`

- `(hB : MeasurableSet B)` (theorem): hB is used only in the two setIntegral_congr_ae applications. Replace each with integral_congr_ae for the restricted measure, followed by `filter_upwards [] with q`; remove `intro hqmem`. The existing pointwise proofs then apply unchanged. MeasurePreserving.setIntegral_image_emb and setIntegral_parabolic_to_product require no measurability assumption on B. Thus the same integral identity and limit hold for arbitrary B, including empty or nonmeasurable B, without integrability assumptions. The identity holds for every ε, including zero.

### [`NavierStokes.PressureStream.reconstructed_divergence_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PressureStream.lean#L773-L791) — `lean-pool-0120`

Snippet: `samples/lean-pool/lean-pool-0120.lean`

- `(hab : a < b)` (theorem): Split on a < b. In that case use the existing proof. Otherwise b ≤ a, and γd is identically zero: when p.1 ≤ a, use TransportPrimitive.radial_zero_of_le hγ.continuous hs; otherwise p.1 > b, so use radial_zero_of_gt hs. This includes b = a. Unfolding weightedSource, normalizeSource, physicalCompact and streamPotential then gives the zero potential, since the integrands vanish. Both reconstructed fields and their derivatives are zero, so the divergence is zero everywhere, including the axis (zero_div).

### [`CKN.Core.HeatPotential.heatPotential_series_representation_of_morrey`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Core/HeatPotential/SubordinatedEnd.lean#L24-L142) — `lean-pool-0121`

Snippet: `samples/lean-pool/lean-pool-0121.lean`

- `(hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)` (theorem): Apply heatPotential_kernel_integrable_on_split with center z := q, evaluation point q, and the same positive radius r. Its ball-membership assumption follows from Metric.mem_closedBall_self hr.le in the parabolic pseudometric. By heatPotential_near_far_cover, this split covers univ, so integrableOn_univ gives global integrability of every kernel-source product. Integrable.integrableOn then supplies hInt for the original split centered at z. The remaining proof is unchanged. This works for arbitrary q, including outside the original ball, and also for zero sources.

### [`PDL.localInterpolantStep_oneSidedR`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/Local.lean#L307-L366) — `lean-pool-0128`

Snippet: `samples/lean-pool/lean-pool-0128.lean`

- `(def_rule : rule = LocalRule.oneSidedR orule YS_def)` (theorem): The instance `localRuleSubsingleton` in `LeanPool/PDL/Local/Rules.lean` makes `LocalRule X YS` a subsingleton. Thus this equality follows from `Subsingleton.elim rule (LocalRule.oneSidedR orule YS_def)`. Delete the binder and derive it locally; the existing proof then works unchanged. This applies to all indices, including empty result sets.

### [`GerverSofa.PartC.Stage2.rhoC_nonneg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MovingSofa/GerverSofa/KernelOnly/Core/Bundle006.lean#L896-L906) — `lean-pool-0129`

Snippet: `samples/lean-pool/lean-pool-0129.lean`

- `(ht : t ∈ Set.Icc (0 : ℝ) T)` (theorem): The result holds for every real t. After unfolding rhoC, the first and last branches are the nonnegative constants 1/2 and 0. In each middle branch, the failed first condition gives params.phi < t; together with phi_nonneg this implies 0 ≤ t, replacing both uses of ht.1. The phase-four proof already uses only its branch conditions via rhoC_phase4_nonneg. Thus the same case-split proof works without ht, including for negative t and t > T.

### [`AVenhance.Infra.Section5.Contracts.sds_gradMatrix_entry_periodic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/Contracts/TermCenteredAnalyticSmooth.lean#L49-L57) — `lean-pool-0130`

Snippet: `samples/lean-pool/lean-pool-0130.lean`

- `(hF : Differentiable ℝ F)` (theorem): Unfolding gradMatrix and spaceGrad gives the scalar derivative of f := fun y => F y j, evaluated at basisVec i. Coordinatewise equivariance gives f(y + latticeShift k) = f y + latticeShift k j. Mathlib's unconditional fderiv_comp_add_right and fderiv_add_const therefore imply fderiv ℝ f (x + latticeShift k) = fderiv ℝ f x; evaluate this equality at basisVec i. No differentiability assumption is needed: translations and adding constants preserve differentiability, so at nondifferentiable points both derivatives are the junk value zero.

### [`RS.LaurentTail.injG_apply_of_not_mem`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/LaurentTail/Comparison.lean#L1239-L1247) — `lean-pool-0131`

Snippet: `samples/lean-pool/lean-pool-0131.lean`

- `[T1Space X]` (variable): The remaining [T2Space X] supplies T1Space X via Mathlib's instance T2Space.t1Space. Thus all definitions in the statement remain available, and the existing dependent-if proof works unchanged. This implication also holds for empty and trivial spaces.

### [`polytopeRoundedSupportCurve_regular`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OperatorTheory/Operator/Crouzeix/SmoothSupportCurve.lean#L231-L242) — `lean-pool-0133`

Snippet: `samples/lean-pool/lean-pool-0133.lean`

- `(hu : u.Nonempty)` (theorem): Split into u = ∅ or u.Nonempty. The nonempty case uses the existing proof. For u = ∅, the partition sum is zero, so Real.log_zero makes polytopeSoftSupport identically zero and polytopeRoundedSupport identically rho. Apply smoothSupportCurve_regular with contDiff_const: deriv_const' and deriv_const reduce its curvature radius to rho, which is positive by hrho. Thus the empty case is also regular.

### [`QuadraticCarleson.packetPoint_abs_sub_right_ge`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/CounterexampleGeometry.lean#L68-L86) — `lean-pool-0135`

Snippet: `samples/lean-pool/lean-pool-0135.lean`

- `(hN : 100 ≤ N)` (theorem): The bound holds for every integer k, independently of N and hk. Put m = k.toNat. Int.self_le_toNat gives k ≤ m, including negative k. From hj and τ < 1/2, k + τ - j < 0. Using abs_of_nonpos and Nat.cast_sub hj, the desired bound reduces to j - m - 1/2 ≤ j - k - τ, which follows by linear arithmetic. Thus hN and hk can even be deleted together.
- `(hk : k ∈ paperBohrIndices N)` (theorem): Replace the proof's equality k.toNat = k by the inequality k ≤ k.toNat from Int.self_le_toNat, cast to ℝ. Together with hj and hτ.2 this makes k + τ - j negative; abs_of_nonpos and Nat.cast_sub hj then reduce the conclusion to linear arithmetic. Negative k cause no problem: toNat truncates to zero, only increasing the available distance. This proof needs neither hk nor hN.

### [`NavierStokes.PhysicalCoordinateBounds.xLift_homogeneous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalCoordinateBounds.lean#L421-L426) — `lean-pool-0136`

Snippet: `samples/lean-pool/lean-pool-0136.lean`

- `(_hy : y ∈ positiveTime)` (theorem): The existing proof works unchanged without _hy. Unfolding xLift and dilation_apply reduces the equality to cancellation of r in (r * y.2.1) / (r * y.1), using Real.rpow_zero and mul_div_mul_left with hr.ne'. This requires no positivity of y.1 and remains valid when y.1 = 0, since the cancellation lemma also covers zero denominators.

### [`NavierStokes.ActivationCone.natural_reference_bounds`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ActivationCone.lean#L819-L863) — `lean-pool-0138`

Snippet: `samples/lean-pool/lean-pool-0138.lean`

- `(hδlim : 2 * δ < ReferencePath.rampLimit)` (theorem): Choose ε using ReferencePath.exists_small_length hδ, so 0 < ε < δ and 2 * ε < rampLimit. Run the displayed compactness argument at ε, obtaining τ₀, α, M. From the definitions of continuation and primitive, slopeCutoff_one and intervalIntegral.integral_congr show that continuation δ G and continuation ε G agree on the open set {p | p.1 < ε}: both cutoffs equal 1 throughout the integration interval. Their Fréchet derivatives therefore agree there by Filter.EventuallyEq.fderiv_eq. Consequently referenceP1 and referenceP2 for widths δ and ε agree there. Taking τ = τ₀ / 2 transfers every bound to width δ and gives 0 < τ ≤ δ. This works for every retained δ > 0, however large; shrinking τ avoids any cutoff-boundary issue.

### [`NavierStokes.TerminalStress.swirlCoefficient_contDiffAt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalStress.lean#L412-L420) — `lean-pool-0158`

Snippet: `samples/lean-pool/lean-pool-0158.lean`

- `(hh1 : h < 1 / 2)` (theorem): Split on h < 1 / 2; the original proof handles that case. Otherwise 2 * h ≥ 1, so the definition of SimilarityCoordinates.coordinateQ gives q h y = 1 for every y. Thus flattening h f y = f (Real.log y.2.1). This is ContDiffAt ℝ 2 at p by hf, smoothness of the projection, and ContDiffAt.log using hs.ne'. The physicalHeat_contDiffAt step still uses only hh, ht, and hs; the final multiplication and division are unchanged. This also covers h = 1 / 2, since h is fixed and q is identically 1 in that case.

### [`NavierStokes.TemporalMeanUpdate.meanClass_axialAlias`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TemporalMeanUpdate.lean#L1535-L1567) — `lean-pool-0159`

Snippet: `samples/lean-pool/lean-pool-0159.lean`

- `(hab : a < b)` (theorem): Split on a < b. The existing proof handles that case. Otherwise logStripData.domain = Prod.fst ⁻¹' Ioo a b is empty, including when a = b. By the definitions of MeanClass and MemClass, smoothness and bounds are then vacuous; choose C = 0 and p = 0.
- `(hh : 0 ≤ h)` (theorem): The required chartPrefactor upper bound holds for every real h. In ChartScales.native_power_bounds, the upper inequality Q n ^ (-1-h) / S n ≤ Tg * Tg ^ nativeIndex h n uses only the unconditional Nat.lt_floor_add_one, not hh. This inequality alone gives timeCoefficient h n ≥ 1 / (Tg * S n), hence chartPrefactor h n ≤ Tg * S n for n ≥ 4. Absorb the four initial bands exactly as in chartPrefactor_bandBound_all. Thus meanClass_desiredIncrement, and consequently this proof, work without hh, including negative h.
- `(hM : ∀ n, M n ≠ 0)` (theorem): The proof uses real_exactAlias_finiteJets only at inverse-frequency exponent 0. Replace that estimate in dividedAlias_global_bounds by TransportPrimitive.iteratedFDeriv_totalIntegral_norm_le, which bounds every jet by the source bound times the radial interval length for arbitrary M, including M = 0. Apply radial_multiplier_finiteJets_uniform to the cutoff derivative, and use exactAlias_supported outside its support, as in exactAlias_sourceJet_bound. The resulting uniform bound needs no division by M; the transfer and interior-support arguments then prove meanClass_dividedAlias and this theorem without hM.

### [`Malliavin.norm_sub_expectationL2_le_mderivD12`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/ClarkOcone.lean#L1095-L1102) — `lean-pool-0164`

Snippet: `samples/lean-pool/lean-pool-0164.lean`

- `(C : ClarkOconeFamily B P 𝓕)` (theorem): The conclusion is the Gaussian Poincaré inequality, independent of a Clark–Ocone family. The checked definitions make mderiv the covariance Cameron–Martin gradient and mderivD12 its graph closure. A direct proof starts with smooth bounded f and the Gaussian Ornstein–Uhlenbeck averaging operators Q_t, centered at the mean of P. Gaussian integration by parts gives Var_P(f) = 2∫₀∞ ‖D Q_t f‖₂² dt; the gradient identity D Q_t f = exp(-t) Q_t(Df) and Jensen give Var_P(f) ≤ 2∫₀∞ exp(-2t)‖Df‖₂² dt = ‖Df‖₂². These identities follow first in finite-dimensional Gaussian coordinates and then by conditional Gaussian approximation, without requiring invertible covariance. Finally, inGraphClosure_mderivClosure supplies smooth bounded approximants converging together with their derivatives; passing to their L² limits proves the stated inequality. The checked expectationL2 definition is precisely the constant expectation. IsGaussian already makes P a probability measure, excluding the zero measure; for a Dirac Gaussian, including trivial W, the centered left side is zero. Thus no Brownian process, filtration property, or data from C is required.

### [`PDL.LoadedCluster.satDown_three_not_basic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/ClusterSatDown.lean#L575-L602) — `lean-pool-0171`

Snippet: `samples/lean-pool/lean-pool-0171.lean`

- `(hΔ : Δ ∈ C.lambdaTwo)` (theorem): This follows from hx and the definition of C.Q. Apply QuasiTab.mem_subtrees_of_atOpt, then induct on QuasiTab.build: expanding build_of_node, the newly introduced type-three node has a label in lambdaTwo; other type-three nodes lie in recursively built children. The build_of_leaf case contains only a type-one node. This argument also covers type-three nodes with empty children. Recover hΔ and use the original proof.
- `(hb : ¬ Δ.basic)` (theorem): Split on Δ.basic. The non-basic case uses the original proof. In the basic case, hS.basicStep Δ hΔ gives C.stepOf Δ = {Y}, hence C.stepOfL Δ = [Y], exactly as established in satDown_build. Then hlen makes next a singleton, hlab supplies its child's label Y, and IH supplies that child's SatDown. Apply the existing satDown_three_basic lemma. The singleton length rules out the empty-child case.
- `(hlen : next.length = (C.stepOfL Δ).length)` (theorem): Only the bound hi' needs replacement. After nonBasicStep produces i and hi, hlab i hi says the child at x ++ [i] has a label. By QuasiTab.labelAt, QuasiTab.atOpt_append and hx, this is impossible unless i < next.length: an out-of-range child lookup returns none. Thus obtain hi' without hlen and retain the remaining proof. If stepOfL is empty, nonBasicStep cannot produce its witness under the satisfaction premises.
- `(hlab : ∀ i, (hi : i < (C.stepOfL Δ).length) → C.Q.labelAt (x ++ [i]) = some ((C.stepOfL Δ)[i]'hi))` (theorem): Recover hlab from hx and the construction of C.Q. Using QuasiTab.mem_subtrees_of_atOpt and induction on QuasiTab.build, every type-three subtree with label Δ has children (C.stepOfL Δ).map (fun Pi => QuasiTab.build C.lambdaTwo C.stepOfL (Δ :: Hist) Pi) for some Hist. This follows directly from build_of_node; build_of_leaf introduces no type-three nodes. QuasiTab.atOpt_child and QuasiTab.build_label then give the required child labels. Empty step lists cause no problem because there are no indices to check. Use this recovered hlab in the original proof.

### [`NavierStokesAndEuler.SmoothCutoff.cutoff_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/ForMathlib/SmoothCutoff.lean#L86-L90) — `lean-pool-0181`

Snippet: `samples/lean-pool/lean-pool-0181.lean`

- `(hR : 0 < R)` (theorem): The remaining hypothesis hx implies R ≥ 0 by norm_nonneg. If R > 0, the original proof applies. If R = 0, unfolding cutoff and using inv_zero and zero_smul gives baseCutoff E 0, which equals 1 by baseCutoff_eq_one since ‖0‖ ≤ 1. Negative R is excluded by hx, so positivity can be deleted.

### [`BooleanIsoperimetry.harper_macaulay_min`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L154-L176) — `lean-pool-0191`

Snippet: `samples/lean-pool/lean-pool-0191.lean`

- `(ha : a ≤ 2 ^ N)` (theorem): Split on a ≤ 2^N; the bounded case uses the original proof. Otherwise, H_mono and H_full give 2^N ≤ H N a, while 2^N ≤ a. Thus the RHS is at least 2^N + 2^N = 2^(N+1), which bounds the LHS by H_le_cube. These lemmas hold also for N = 0 and zero inputs. Both ha and hb can even be deleted together.
- `(hb : b ≤ 2 ^ N)` (theorem): Split on b ≤ 2^N; the bounded case uses the original proof. Otherwise, H_mono and H_full give 2^N ≤ H N b, while 2^N ≤ b. The two maxima therefore sum to at least 2^(N+1), and H_le_cube bounds the LHS by that number. This includes N = 0 and zero inputs. Both bounds can even be deleted together.

### [`PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PebblingLean/UpperBoundParameters.lean#L2099-L2138) — `lean-pool-0205`

Snippet: `samples/lean-pool/lean-pool-0205.lean`

- `(hsmall : splitM K n < n)` (theorem): It follows from hslack. At n = 0, loss n = 0, contradicting hslack. At n = 1, splitM K 1 = 0 by its definition and Real.log_one, Real.sqrt_zero, and Nat.ceil_zero. For n ≥ 2, if n ≤ splitM K n, then splitA K n = 0, so hslack gives 1 ≤ loss n. But loss_le_of_le gives loss n ≤ loss 2 = 1/4, a contradiction. Derive hsmall this way, then use the existing proof unchanged.

### [`LeanPool.Besicovitch.exists_nonnegative_score_of_matched_endpoint_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Besicovitch/SixPoint/EndpointFailureClosed.lean#L27-L46) — `lean-pool-0208`

Snippet: `samples/lean-pool/lean-pool-0208.lean`

- `(hlambda : 0 < lambda)` (theorem): The conclusion follows from h alone: apply sixPointFiniteProperty_barS_of_weightedGeometricBound gramLambda_pos gramMu_pos weightedGeometricBound_gram to configuration and h. SixPointFiniteProperty is defined to give exactly this conclusion for every admissible configuration. To avoid circular dependence on this endpoint lemma, retain its original proof as a local auxiliary and reproduce the assembly in EndpointPacking.lean using that auxiliary and the independently proved Gram bound. Thus no positivity condition on the supplied lambda is needed, including when lambda is zero or negative.
- `(hmu : 0 < mu)` (theorem): The same unconditional finite-property argument described above proves the conclusion from h, using the fixed positive weights gramLambda and gramMu rather than the supplied mu. It therefore also covers zero and negative mu.
- `(hmatching : SelectedDiagonalMatchingFails configuration)` (theorem): The same finite-property argument proves the conclusion for every configuration satisfying h, without a selected-matching assumption. Its assembly handles both matching alternatives and the already-successful packing case; the original endpoint proof can be retained locally to avoid circularity.
- `(hred : redSiblingTriangleFailure configuration (.endpoint 0))` (theorem): The same finite-property argument proves the conclusion from h alone. The assembly in EndpointPacking.lean handles successful sibling packings and either surviving matched endpoint, so this particular red endpoint failure is unnecessary. Retaining the original endpoint proof as a local auxiliary avoids circularity.
- `(hblue : blueSiblingTriangleFailure configuration (.endpoint 0))` (theorem): The same finite-property argument proves the conclusion from h alone, including configurations without this blue endpoint failure. As above, the original endpoint proof can be used as a local auxiliary in the finite-property assembly without circularity.
- `(hweighted : weightedPairScore configuration.rootDisplacement barC lambda mu (configuration.redDisplacement .left) (configuration.redDisplacement .right) (configuration.bluePullback .left) (configuration.bluePullback .right) ≤ 0)` (theorem): The same finite-property argument proves the conclusion from h alone. weightedGeometricBound_gram supplies the needed bound at the fixed weights gramLambda and gramMu, independently of the supplied weights and their score. All six reported hypotheses can be removed simultaneously.

### [`NavierStokes.PhysicalParticularWave.bandPressureMode_eq_physical`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalParticularWave.lean#L1179-L1206) — `lean-pool-0212`

Snippet: `samples/lean-pool/lean-pool-0212.lean`

- `(hKr : referenceFrequency D j ≠ 0)` (theorem): Split on whether referenceFrequency D j is zero. The nonzero case uses the existing proof. In the zero case, referencePressure vanishes because copyPressure divides by that frequency. Also normalWeight is zero, so the transported normal is zero; TangentProjection.pressureCoefficient then has zero denominator and is zero. Thus bandPressure also vanishes. Unfolding complexCopyPressure, commonPressure, periodizedCopies and mode reduces both sides to zero.
- `(hz : 0 < z.2 0)` (theorem): Its only uses are through cylinderChange_graph, whose identity holds for every real radius. Strengthen commonGraph_radialScale using (a*r)^b = a^b*r^b for a > 0 and arbitrary r: for r ≥ 0 use Real.mul_rpow; for r < 0 use Real.rpow_def_of_neg, Real.rpow_def_of_pos, Real.log_mul and exponential addition. The nonnegative case includes r = 0, even when b = 0. The existing proofs of commonGraph_map and cylinderChange_graph then work without radius positivity, and the rest of this proof is unchanged.

### [`AleksandrovDifferentiability.prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/AleksandrovDifferentiability/Analysis/GoodSet.lean#L97-L106) — `lean-pool-0218`

Snippet: `samples/lean-pool/lean-pool-0218.lean`

- `(hs : MeasurableSet s)` (theorem): After applying ae_iff to each hsection x, Measure.measure_inter_eq_zero_of_restrict shows that the section of s \ G has ν-measure zero without any measurability assumption on s. Use hbad.exists_measurable_subset_ae_eq to obtain a measurable subset t agreeing almost everywhere with s \ G. Its sections are null by monotonicity, so Measure.measure_prod_null proves t null; measure_congr finishes. These steps also cover empty sets and zero measures.
- `[SFinite ν]` (theorem): Repeat the referenced proof, replacing the use of Measure.measure_prod_null by Measure.measure_prod_null_of_ae_null, which requires no SFinite instance. The same section argument proves the required almost-everywhere nullity. Moreover, Measure.prod is defined to be zero when ν is not s-finite, so that case holds automatically. This hypothesis and hs can also be deleted simultaneously.

### [`Zeta5Irrational.cov_302_304`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta5Irrational/Table/Intervals.lean#L7296-L7302) — `lean-pool-0219`

Snippet: `samples/lean-pool/lean-pool-0219.lean`

- `0 < t (proof argument h0)` (theorem): The lower bound h1 already implies positivity: `have h0 : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 723732917263 / 2560000000000) h1`. After deleting the positivity argument, derive h0 this way and reuse the original case split with tc_302 and tc_303 unchanged. The strictly positive lower endpoint excludes zero and negative t.

### [`TauCeti.DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_reducingSubspace`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/SinTheta/Natural/Reducing.lean#L496-L543) — `lean-pool-0223`

Snippet: `samples/lean-pool/lean-pool-0223.lean`

- `(hAdense : Dense (A.domain : Set ER))` (theorem): Replace its use in the problem record with hA.dense_domain, by Mathlib's IsSelfAdjoint.dense_domain. This includes trivial spaces and excludes nondense-domain junk cases automatically.
- `(hAclosed : A.IsClosed)` (theorem): Replace its use in the problem record with hA.isClosed, by Mathlib's IsSelfAdjoint.isClosed. This holds without nontriviality assumptions.
- `(hA0dense : Dense (A0.domain : Set FR))` (theorem): Replace its use in the problem record with hA0.dense_domain, by Mathlib's IsSelfAdjoint.dense_domain. This includes trivial spaces and handles the adjoint's nondense-domain junk convention.
- `(hA0closed : A0.IsClosed)` (theorem): Replace its use in the problem record with hA0.isClosed, by Mathlib's IsSelfAdjoint.isClosed. This holds also for trivial spaces. All four reported hypotheses can be deleted simultaneously.

### [`BGS.CorvajaZannier.exists_support_direction_of_not_rankTwo`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveSupportRank.lean#L186-L216) — `lean-pool-0224`

Snippet: `samples/lean-pool/lean-pool-0224.lean`

- `(hnonsingleton : ∃ s ∈ f.support, s ≠ r)` (theorem): Split on whether such an s exists. If so, use the existing proof. Otherwise every s ∈ f.support equals r, so planeExponentDifference r s is zero by its definition. Choose the nonzero vector v := fun _ => (1 : ℤ) and k := 0 for every s. The retained hypothesis hr rules out empty support.

### [`ViscositySolns.SmoothConvexApproximationOnInteriorClosedBallTheorem.of_extensionMollification`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Jensen/ConvexMollification.lean#L285-L308) — `lean-pool-0232`

Snippet: `samples/lean-pool/lean-pool-0232.lean`

- `(hmoll : ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem n)` (theorem): MainTheorems.lean:42–86 proves ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem.proof unconditionally, without using this theorem. Its independent normalized-bump convolution construction can be moved or inlined here, replacing hmoll in the existing proof. It applies to every n, including n = 0; the required radius inequalities 0 < r < R remain part of the conclusion's definition.

### [`CarlsonFunctions.SeveralComplexVariables.norm_sub_le_of_separately_analytic_bounded`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CarlsonFunctions/SeveralComplexVariables/LocallyBounded.lean#L67-L108) — `lean-pool-0237`

Snippet: `samples/lean-pool/lean-pool-0237.lean`

- `(hr : 0 < r)` (theorem): Split on 0 < r, using the existing proof in the positive case. Otherwise, Metric.nonneg_of_mem_closedBall hx gives 0 ≤ r, hence r = 0. By Metric.closedBall_zero, hx and hy then force x = c and y = c, so the conclusion simplifies to 0 ≤ 0 (with M / 0 = 0). Negative radii are impossible by hx. This also covers empty ι and trivial F.

### [`EulerPacketTerminalDatum.forwardInitializedPacket_normalized_bound`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/PacketForwardInitializedCorrectionData.lean#L76-L84) — `lean-pool-0242`

Snippet: `samples/lean-pool/lean-pool-0242.lean`

- `(hα : 0 < α)` (variable): Evaluate hgrowth at t₀ = ⟨0, le_rfl, D.T_pos.le⟩. By timeProfileChange_pos and S.growth_pos, its left side is positive; by L.initial_one, its right side is α. Thus 0 < α follows from the remaining hypotheses, and the existing proof can use this derived fact. The time interval is nonempty because D.T_pos holds.
- `(hN : 1 ≤ N)` (theorem): Split on N = 0. For positive N, use the existing proof. For N = 0, sourcePacketPullbackField_path is a sum over Finset.range 0, hence zero; smul_path shows the normalized field also has zero path. WordBound therefore has zero left-hand side. Its right-hand side is nonnegative by BC.multiplierCost_nonneg, fixedVelocityGradeCost_nonneg, and L.radius_one, so the bound holds in this missing case too.

### [`LeanPool.Besicovitch.sigma_mul_radius_div_two_le_diam_localAttachmentComponent`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Besicovitch/Rectifiability/ComponentDiameter.lean#L38-L191) — `lean-pool-0244`

Snippet: `samples/lean-pool/lean-pool-0244.lean`

- `(hsigma : 0 ≤ sigma)` (theorem): Split on 0 ≤ sigma. The existing proof handles that case. Otherwise, hrho gives sigma * rho / 2 ≤ 0, so the conclusion follows from Metric.diam_nonneg, which also holds for empty and unbounded sets.
- `(hsigma_one : sigma < 1)` (theorem): Its only use is establishing sigma * rho / 2 < rho. Extract w from hannulus. Metric.mem_ball and nonmembership in the inner ball give sigma * rho / 2 ≤ dist w z < rho. This replaces that step, and the remaining proof is unchanged.
- `(hchosen : chosen ⊆ badConvexSets mu F alpha)` (theorem): Only the compactness argument uses it, and that argument works for arbitrary chosen under hF and hsum. Adapt isCompact_compactAttachmentUnion: retain the finite-large-attachments argument using ENNReal.finite_const_le_of_tsum_ne_top and isCompact_convexAttachment. For a small W, its finite extended diameter implies boundedness by Metric.isBounded_iff_ediam_ne_top, so ediam_convexAttachment_le applies. If F ∩ diameterThickening 2 W is empty, its attachment is empty by convexHull_empty and closure_empty. Otherwise choose f in this intersection; f belongs to F and its attachment, so the attachment's small diameter places it in the required neighborhood of F. This replaces every use of hchosen in the compactness proof; the rest of the theorem is unchanged. Empty families and empty attachments are covered.
- `(hrho : 0 < rho)` (theorem): Extracting w from hannulus gives hw_outer : w ∈ Metric.ball z rho. Then Metric.pos_of_mem_ball hw_outer recovers hrho, allowing the existing proof unchanged. Nonpositive rho is already excluded by hannulus.

### [`EulerTransversePacketProvider.Forcing.velocityPath_reflection_neg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/TransversePacketParity.lean#L374-L380) — `lean-pool-0247`

Snippet: `samples/lean-pool/lean-pool-0247.lean`

- `(hSym : ∀ x, -x ∈ D.support ↔ x ∈ D.support)` (variable): Enlarge the auxiliary support to Set.univ, whose reflection symmetry is automatic. The canonical continuous linear inclusions from Supported P V D.support D.support_measurable into the corresponding univ-supported spaces intertwine the coefficient operators: this follows from supportedOperatorMap_coe and supportedOperator_eq_square. EulerLinearDuhamel.Evolution.solution_map therefore identifies the original coordinate solution with the univ-supported solution; projectedForcing and physicalVelocity also commute with these inclusions by their multiplier definitions. Apply EulerSourceCylinderParity.velocity_reflection_neg on univ and transfer its equality back to the original fullVelocityPath. No compactness of univ is required by that lemma or the evolution construction. This argument also covers empty support and zero data.
- `(hM : ∀ t x, D.M.field t (-x) = D.M.field t x)` (variable): Replace D.frameDerivative_even hF hM in the proof by evenness obtained from differentiating D.frame_even hF in time. Specifically, D.frame_derivative at x and -x gives derivatives of identical clamped time functions, since frame_even holds at every clamped time. HasDerivWithinAt.derivWithin identifies their derivatives using uniqueDiffOn_Icc D.T_pos, yielding D.frameDerivative.field t (-x) = D.frameDerivative.field t x. This supplies exactly the coefficient parity required by velocity_reflection_neg without hM. The retained strict positivity D.T_pos ensures uniqueness even at both endpoints; no nontriviality assumption on U or nonzero-data assumption is needed.

### [`Zeta5Irrational.tc_361`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta5Irrational/Table/Intervals.lean#L2671-L2676) — `lean-pool-0249`

Snippet: `samples/lean-pool/lean-pool-0249.lean`

- `0 < t` (theorem): The retained lower bound implies positivity: `norm_num` proves `(0 : ℝ) < 46687825988961 / 128000000000000`, and `linarith` then gives `0 < t`. Supply this derived fact to the existing `check_right` application. Zero and negative t remain excluded by the lower bound.

### [`CKN.norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Poincare/Lp.lean#L159-L202) — `lean-pool-0254`

Snippet: `samples/lean-pool/lean-pool-0254.lean`

- `[MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]` (theorem): By ENNReal.toReal_pos_iff, hvol implies volume U < ∞. Since volumeMeasureOn U is volume.restrict U, MeasureTheory.isFiniteMeasure_restrict supplies the deleted instance locally, after which the original proof applies. Zero and infinite volume are already excluded by hvol.
- `(hu : MeasureTheory.IntegrableOn u U)` (theorem): The segment estimate norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment bounds ‖u x - u y‖ by the integrable function in hsegment. ContDiff.continuous and Continuous.aestronglyMeasurable give measurability of y ↦ u x - u y, so MeasureTheory.Integrable.mono' makes this difference integrable on U. The constant u x is integrable under the retained finite-measure instance; subtracting the difference using Integrable.sub recovers hu. The original proof then applies. This works also for d = 0; hvol already excludes zero-volume domains.

### [`Bananas.TwiceMarkedBananas.s5_lem5_3_1`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BrillNoetherGraphs/TwiceMarkedBananas.lean#L2116-L2135) — `lean-pool-0261`

Snippet: `samples/lean-pool/lean-pool-0261.lean`

- `(hconn : graphConnected M.graph)` (theorem): Connectivity follows from hTau alone. Write R(a,b) = rank(D + a•oneChip u - b•oneChip v). For any natural n, choose A ≥ tau b for 0 ≤ b ≤ n, and L ≤ all those values sufficiently negative that R(L-1,0) = R(L-1,n+1) = -1. Summing hTau.2 over L ≤ a ≤ A and 0 ≤ b ≤ n telescopes to R(A,0) - R(A,n+1) = n+1. Thus R(A,0) ≥ n, using rank_geq_neg_one; the boundary vanishing uses rank_neg_one_of_deg_neg. These lemmas require no connectivity and transfer through rank_toLib. Conversely, a disconnected graph has a nonempty edge-isolated cut S not containing u. Summation over S annihilates every firing vector, hence every principal divisor. Consequently rank(D + A•oneChip u) ≤ max(-1, ∑ x∈S, D x), uniformly in A: removing sufficiently many chips at any vertex of S makes its cut degree negative and therefore unwinnable. This contradicts the arbitrarily large ranks just obtained. The graph is nonempty by its structure, singleton graphs are connected, and coincident marks do not affect this argument. Derive hconn this way, then use the existing proof unchanged.

### [`EGZ.CommonMeasure.final_mass_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ErdosGinzburgZiv/EGZ/Decomposition/CommonMeasure.lean#L109-L119) — `lean-pool-0276`

Snippet: `samples/lean-pool/lean-pool-0276.lean`

- `(hε : 0 < ε)` (theorem): Split on 0 < ε. In the positive case, use the existing proof. Otherwise ε ≤ 0, and WeightedIncidence.mass_nonneg applied with hu gives nonnegative masses for P and Q. Thus ε / 2 * mass u P ≤ 0 ≤ mass u Q. This includes ε = 0 and empty α.
- `(hR : 0 < R)` (theorem): Split on 0 < R. In the positive case, use the existing proof. Otherwise mass_weight_mono w u hle P and hP give mass u P ≤ R ≤ 0. Since mass_nonneg u hu P gives the reverse bound, mass u P = 0. The conclusion then follows from mass_nonneg u hu Q. This covers R = 0 and empty α; negative R is incompatible with these bounds.

### [`eigenvector_constant_sign`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SpectralPositivity/Operator/JentzschProof.lean#L332-L387) — `lean-pool-0280`

Snippet: `samples/lean-pool/lean-pool-0280.lean`

- `(hT_compact : IsCompactOperator T)` (theorem): Its only use is passing it to abs_eigenvector_of_top_eigenvector. That lemma's proof never uses its _hT_compact argument. Inline that proof without compactness; the remaining proof is unchanged. This works for arbitrary measure spaces, including degenerate ones.
- `(hT_sa : IsSelfAdjoint T)` (theorem): A direct argument avoids self-adjointness. Put h = |f|, u = h + f and v = h - f, both nonnegative. If both are nonzero, positivity improvement gives ⟨u,Tv⟩ > 0 and ⟨v,Tu⟩ > 0. Indeed, L2.inner_def and L2.integrable_inner reduce this to nonnegative integrable products; integral_eq_zero_iff_of_nonneg_ae and Lp.eq_zero_iff_ae_eq_zero exclude zero integrals. Bilinearity gives 2(⟨h,Th⟩ − ⟨f,Tf⟩) = ⟨u,Tv⟩ + ⟨v,Tu⟩ > 0, contradicting hlam₀_top, hf_eigen and ‖|f|‖ = ‖f‖. Thus u or v is zero, so f or −f is nonnegative and nonzero. Apply ground_state_strictly_positive to that eigenvector. Empty or zero-measure cases contradict hf_ne.
- `(hlam₀ : 0 < lam₀)` (theorem): This follows from the remaining assumptions. Set h = |f|, which is nonnegative and nonzero by hf_ne. Positivity improvement makes Th strictly positive almost everywhere, hence ⟨h,Th⟩ > 0: use L2.inner_def, L2.integrable_inner and integral_eq_zero_iff_of_nonneg_ae; a zero integral would force h = 0 by Lp.eq_zero_iff_ae_eq_zero. Then hlam₀_top gives 0 < ⟨h,Th⟩ ≤ lam₀ * ‖h‖², forcing lam₀ > 0. Recover this fact and use the original proof. Integrability rules out junk integral values; hf_ne excludes zero-measure and trivial Lp cases.

### [`QuadraticCarleson.annularQuadraticKernel_correlation_le_ordered`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/QuadraticFixedHeightAveragingCorrelation.lean#L49-L127) — `lean-pool-0281`

Snippet: `samples/lean-pool/lean-pool-0281.lean`

- `(hR : 0 < R)` (theorem): Split on 0 < R. The positive case uses the existing proof. Otherwise, div_nonpos_of_nonneg_of_nonpos gives D / R ≤ 0, including R = 0. Together with hab and norm nonnegativity, this forces a identically zero. The integral is therefore zero, while the majorant is nonnegative by its definition, hS, hu, and nonnegativity of D².
- `(hS : 0 < S)` (theorem): Recover hS as hR.trans_le hRS, then use the unchanged proof. Thus no additional zero or negative S cases arise.
- `(hH : 0 < H)` (theorem): Since hu gives u⁵ > 0, hdecay implies H > 0: H ≤ 0 would give H * u⁵ ≤ 0, contradicting 1 ≤ H * u⁵. Recover hH and retain the existing proof.
- `(hD : 0 ≤ D)` (theorem): From norm_nonneg (a 0) and hab 0 obtain 0 ≤ D / R. Multiplying by the positive R gives 0 ≤ D. Recover hD and retain the existing proof; D = 0 is allowed.
- `(hu : 0 < u)` (theorem): Recover hu from hH and hdecay. If u ≤ 0, its odd power u⁵ is nonpositive, hence H * u⁵ ≤ 0, contradicting hdecay. The existing proof then applies.
- `(hu1 : u ≤ 1)` (theorem): Split on u ≤ 1 and use the existing proof in that case. For u > 1, norm_phase and the amplitude bounds bound the integrand norm by D²/(R*S). Its support lies in [x-R, x-R/4], so intervalIntegral.norm_integral_le_of_norm_le_const gives an integral norm at most D²/S. Outside |x-y| ≤ 2*S the integrand vanishes by the support assumptions and hRS. Inside, the defined majorant is at least 2*D²/S, since both possible inner factors are at least 1. This also covers D = 0.
- `(hlam' : lam * R ^ 2 ≤ 4 * H)` (theorem): In the call to norm_integral_quadraticTTStar_fixed_height_supported, replace the height by H₁ = lam * R². It is positive and at least H by hH and hlam. Consequently hdecay and hμ' remain valid at H₁; the lower lambda bound is equality and the upper bound H₁ ≤ 4*H₁ follows from positivity. The conclusion of that lemma is independent of height, so the remaining proof is unchanged.

### [`AVenhance.Infra.Section3.ChiMKCorrector.chiMK_spaceLap_three_active`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section3/ChiMKCorrector.lean#L159-L209) — `lean-pool-0282`

Snippet: `samples/lean-pool/lean-pool-0282.lean`

- `(hk : k % 4 = 3)` (theorem): Split on k % 4 = 3. The true branch uses the existing proof. Otherwise, component 0 of uShear is identically zero: its k % 4 = 1 branch has first coordinate zero, and its remaining branch is the zero vector. Thus Ingredients.chiMK also has component 0 identically zero, regardless of κ, t, or x. Apply the preceding lemma ChiMKCorrector.chiMK_spaceLap_of_zero_component to obtain the conclusion. These branches cover every integer k.

### [`TauCeti.sum_sq_principalCosines_eq_sum_sq_norm_projection`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean#L747-L767) — `lean-pool-0283`

Snippet: `samples/lean-pool/lean-pool-0283.lean`

- `[U.HasOrthogonalProjection]` (theorem): FiniteDimensional.finiteDimensional_submodule supplies finite-dimensionality of U. The instance RCLike.properSpace_submodule gives ProperSpace U, hence complete_of_proper gives CompleteSpace U, and Submodule.HasOrthogonalProjection.ofCompleteSpace supplies the deleted instance. The statement still elaborates and the existing proof works unchanged. This includes U = ⊥ and zero-dimensional E. Both projection hypotheses can be deleted together.
- `[V.HasOrthogonalProjection]` (theorem): FiniteDimensional.finiteDimensional_submodule supplies finite-dimensionality of V. The instance RCLike.properSpace_submodule gives ProperSpace V, hence complete_of_proper gives CompleteSpace V, and Submodule.HasOrthogonalProjection.ofCompleteSpace supplies the deleted instance. The statement still elaborates and the existing proof works unchanged, including V = ⊥ and zero-dimensional E. Both projection hypotheses can be deleted together.

### [`Malliavin.memLp_mderiv_cylinder_expGrowth`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/CylindricalGrowth.lean#L488-L496) — `lean-pool-0295`

Snippet: `samples/lean-pool/lean-pool-0295.lean`

- `(hC : 0 ≤ C)` (theorem): Evaluating hfg' at y = 0 gives ‖fderiv ℝ f 0‖ ≤ C, since exp (c * ‖0‖) = 1. Nonnegativity of the norm therefore implies 0 ≤ C. Recover hC this way and use the existing proof. This also works when n = 0.
- `(hc : 0 ≤ c)` (theorem): Since c ≤ |c| and norms are nonnegative, Real.exp_le_exp implies C * exp (c * ‖y‖) ≤ C * exp (|c| * ‖y‖), using hC. Strengthen hfg' to this bound and use the existing dominated proof with expGrowth_coord_le hC (abs_nonneg c) L and integrable_expGrowth_sq μ C |c| _. This handles negative c, C = 0, and n = 0 without changing the conclusion.

### [`Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_of_generated`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/BrownianPurePowerDuality.lean#L393-L402) — `lean-pool-0298`

Snippet: `samples/lean-pool/lean-pool-0298.lean`

- `(hsm : ∀ t, StronglyMeasurable (B t))` (theorem): Recover it as `have hsm : ∀ t, StronglyMeasurable (B t) := fun t => (generated.measurable t).stronglyMeasurable`, then use the original proof. The library's `IsWienerGenerated.measurable` supplies coordinate measurability, and Mathlib's `Measurable.stronglyMeasurable` applies because the target ℝ is second-countable. This implication requires no nondegeneracy assumptions and covers trivial spaces as well.


## FLT (Anthropic) (78 flagged)

### [`P2MW.S_ModularCurve_full_eq_adjoin_primes.ModularCurve.W1.roots_prime_at_slot_roots_nodup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_full_eq_adjoin_primes.lean#L306-L312) — `flt-anthropic-0001`

Snippet: `samples/flt-anthropic/flt-anthropic-0001.lean`

- `(hζ : IsPrimitiveRoot (ζ : K) N)` (theorem): The conclusion is independent of N and ζ. Set L = CyclotomicField p K. Since K has characteristic zero and p is prime, CyclotomicField.isCyclotomicExtension and IsCyclotomicExtension.exists_isPrimitiveRoot supply a primitive p-th root, hence a unit η. Apply roots_prime_at_slot and roots_prime_at_slot_nodup over L with N := p, ζ := η and p ∣ p. The injective map coeffMap (algebraMap K L) carries the original polynomial to this polynomial: use coeffMap_qExpand, and coefficientwise compatibility with qTwist and coeffEmb. Descend nodup using Polynomial.map_roots_le_of_injective, Multiset.nodup_of_le and Multiset.Nodup.of_map. This does not use hζ or hpN.
- `(hpN : p ∣ N)` (theorem): Use the same cyclotomic-extension proof described for hζ: over CyclotomicField p K, choose a primitive p-th root and apply the two preceding lemmas with auxiliary level p, then descend nodup through the injective coefficient map. No relation between p and the original N is used. Empty root multisets cause no issue because map_roots_le_of_injective and nodup descent also cover them.
- `[NeZero N]` (theorem): IsPrimitiveRoot is defined without a nonzero-order instance, and no other remaining binder or conclusion requires NeZero N. The cyclotomic-extension argument described above ignores the original N entirely and therefore also proves the N = 0 case. Its auxiliary level is p ≠ 0; e remains nonzero and K remains a characteristic-zero field. These three hypotheses can all be deleted together.

### [`P2MW.S_ModularCurve_FullLevel_mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin.P3aW_node14.chartAlgFin_eq_of_mem_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_mem_of_coe_mem_nonunits_of_isMaximal_of_mem_ssJSet_chartAlgFin.lean#L96-L99) — `flt-anthropic-0008`

Snippet: `samples/flt-anthropic/flt-anthropic-0008.lean`

- `[Fact (a ≠ 0)]` (theorem): chartAlgFin R F a is defined as the elements integral over Algebra.adjoin R {a}, without requiring a ≠ 0. The preceding chartAlgFin_le_of_mem proof works unchanged after removing both nonzero assumptions: it uses inclusions and isIntegral_trans only. Applying this generalized inclusion in both directions proves the equality, including when a = 0. Both Fact hypotheses can be deleted together.
- `[Fact (b ≠ 0)]` (theorem): chartAlgFin R F b requires no nonzero assumption. Generalize the preceding chartAlgFin_le_of_mem by deleting its two Fact binders; its existing integral-transitivity proof still works unchanged. Applying it to hab and hba proves the equality even when b = 0. Both Fact hypotheses can be deleted together.

### [`P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.C2idemCore.IdempotentOrbit.exists_idempotent_orbit_or_isField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.lean#L172-L278) — `flt-anthropic-0014`

Snippet: `samples/flt-anthropic/flt-anthropic-0014.lean`

- `[Finite ι]` (theorem): Finiteness follows from the remaining hypotheses. For nonempty ι, let t = conj φ s. Since t^[n] = id and hn.pos, t is an automorphism. Coordinatewise IsIdempotentElem.iff_eq_zero_or_one shows that the minimal nonzero idempotents of the product are exactly ind {j}. Thus t permutes them, inducing a permutation ψ with ψ^[n] = id. Choose j and form its finite orbit S. The identity ind_eq_sum shows that ind S is t-fixed. The supplied proof of hfix01 requires no finiteness, so φ.symm (ind S), being nonzero and fixed, equals 1. Evaluating ind S = 1 at every coordinate shows that S contains every index. Consequently Set.finite_univ_iff supplies Finite ι; install this instance and continue with the existing proof. If ι is empty, the original subsingleton argument gives the zero witness without finiteness.

### [`P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6.comp_heckeDiag_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.lean#L664-L678) — `flt-anthropic-0018`

Snippet: `samples/flt-anthropic/flt-anthropic-0018.lean`

- `(hp : p ≠ 0)` (theorem): Split on whether p = 0. For p ≠ 0, use the existing proof. For p = 0, ModularForm.heckeDiagMatrix_zero states that heckeDiagMatrix 0 = 1, so one_smul reduces the conclusion to hF. Thus the excluded zero case also holds.

### [`P2MW.S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.AlgebraicGeometry.RelPicard.ChartHypotheses.exists_cover_chart_of_cover`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelPicard_eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one_of_supportedIn.lean#L154-L166) — `flt-anthropic-0028`

Snippet: `samples/flt-anthropic/flt-anthropic-0028.lean`

- `(hDU : D.SupportedIn U)` (theorem): The definition of RelEffCartierDiv already supplies D.flat: its closed subscheme is flat over T. Consequently its ideal module commutes with this base change without any support condition. Locally, for Spec B over Spec A in T with ideal J, B/J is A-flat, so tensoring 0 → J → B → B/J → 0 with k remains exact. This identifies J ⊗_B (B ⊗_A k) with the base-changed ideal. These canonical identifications glue, replacing the invertibility-based construction of eI in nonempty_chartModule_iso. The sectionTwist isomorphism still follows from nonempty_pullback_sectionTwist_iso_of_range_subset using the remaining assumptions; the tensor and cover arguments are unchanged. This works also for degree zero, r = 0, and empty schemes.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.CHRAux.Tr_fixed`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.lean#L97-L99) — `flt-anthropic-0032`

Snippet: `samples/flt-anthropic/flt-anthropic-0032.lean`

- `[DecidableEq G]` (variable): Use `omit [DecidableEq G] in`: the existing proof still works unchanged. The definition of Tr uses only Fintype enumeration and finite summation, neither requiring decidable equality. Equiv.mulLeft and Fintype.sum_equiv likewise require no DecidableEq instance. The reindexing argument also works for the trivial group and zero ring; an empty group is excluded by Group.

### [`P2MW.S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator.D628.coe_bar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_IgusaScheme_exists_spBase_and_cuspChart_centrePin_of_genericFibre_iso_ofGenerator.lean#L382-L384) — `flt-anthropic-0034`

Snippet: `samples/flt-anthropic/flt-anthropic-0034.lean`

- `[NeZero p]` (variable): Use `omit [NeZero p] in`; the same `rfl` proof works. The definitions of `modularFunctionFieldFull`, `laurentBaseChange`, and `bar` do not require this instance. In particular, `modularFunctionFieldFull` is the intermediate field generated by divisor expansions, also defined at p = 0, and `bar` simply packages the coefficient embedding. Its coercion is definitionally that embedding even at p = 0.

### [`P2MW.S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.Blk176Arith.not_cube_dvd_mul_prod_filter`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.lean#L147-L182) — `flt-anthropic-0038`

Snippet: `samples/flt-anthropic/flt-anthropic-0038.lean`

- `(hN0 : N ≠ 0)` (theorem): It follows from hN3 q hq: if N = 0, then dvd_zero (q ^ 3) contradicts hN3 q hq. After deleting the binder, derive hN0 locally by this argument and reuse the original proof unchanged. Thus the zero case is excluded by the remaining hypotheses, including when S is empty.

### [`P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.WeierstrassCurve.Affine.isPrincipal_of_geomDivisorSum_eq_zero'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean#L2026-L2070) — `flt-anthropic-0040`

Snippet: `samples/flt-anthropic/flt-anthropic-0040.lean`

- `[HasPrincipalDivisors F W.FunctionField]` (theorem): The library theorem WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed (Theorems/Thm_WeierstrassCurve_Affine_hasPrincipalDivisors_of_isAlgClosed.lean:8) derives this instance from [Field F], [IsAlgClosed F], and [W.IsElliptic], all retained here. Import that theorem and start the proof with `letI := _root_.WeierstrassCurve.Affine.hasPrincipalDivisors_of_isAlgClosed W`; the existing proof then works unchanged. The lemma applies in every characteristic without extra nonvanishing assumptions; the proof still establishes f ≠ 0, and D = 0 is covered.

### [`P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.P2mS17LB.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.lean#L49-L111) — `flt-anthropic-0046`

Snippet: `samples/flt-anthropic/flt-anthropic-0046.lean`

- `(hn : 0 < n)` (theorem): The retained hqn implies n ≠ 0, since every natural number divides 0. Thus recover 0 < n and use the original proof; the zero case is impossible.
- `(hqn : ¬ (q : ℕ) ∣ n)` (theorem): Take a finite Galois intermediate field K containing F₀, ζ and α, using adjoining and normal closure. Let σ be the restriction of primeLocalToGlobal q φ to K and r = orderOf σ. Finite.algHom and Finite.algEquiv give finiteness, so orderOf_pos and pow_orderOf_eq_one give r > 0 and σ^r = 1. Apply exists_level_dvd_of_frobenius_pow_mem_inertia_sup with base K and positive level r * (n * d), then take normal closure F. By H_anti, membership in H q F forces this level to divide m. Hence n*d divides m and σ^m = 1, which fixes α by AlgEquiv.restrictNormalHom_apply. This works even when q divides n.
- `(hζ : IsPrimitiveRoot ζ n)` (theorem): The finite-order construction described for hqn works for arbitrary ζ: adjoin ζ and α to F₀, take finite normal closure K, and let r > 0 be the order of the restricted automorphism. Force r*(n*d) to divide the relevant exponents using exists_level_dvd_of_frobenius_pow_mem_inertia_sup, then take normal closure. These exponents fix α and are divisible by n*d. No root-of-unity property is needed; ζ = 0 also causes no problem.
- `(hα : α ^ n = ((q : ℕ) : AlgebraicClosure ℚ))` (theorem): Every α in AlgebraicClosure ℚ belongs to a finite Galois intermediate field K containing F₀ and ζ. The restriction of primeLocalToGlobal q φ to K has positive finite order r. Apply exists_level_dvd_of_frobenius_pow_mem_inertia_sup at level r*(n*d), and take normal closure. H_anti gives r*(n*d) ∣ m, so the restricted m-th power is the identity and fixes α. Thus the power equation is unnecessary, including when α = 0.

### [`P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.PLCDSol.exists_gamma0_apply_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.lean#L883-L889) — `flt-anthropic-0048`

Snippet: `samples/flt-anthropic/flt-anthropic-0048.lean`

- `[NeZero M]` (variable): Split on M = 0. For M ≠ 0, install NeZero M and use the existing proof. For M = 0, ZMod 0 is definitionally ℤ; Int.units_eq_one_or gives d = 1 or d = -1. Choose respectively I or -I in SL(2, ℤ). Each has lower-left entry zero, so belongs to Gamma0 0 by CongruenceSubgroup.Gamma0_mem, and its upper-left entry equals d. Thus the excluded zero case also holds.

### [`P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.CohCarrier.gammaH_inf_gamma0_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.lean#L104-L128) — `flt-anthropic-0049`

Snippet: `samples/flt-anthropic/flt-anthropic-0049.lean`

- `[NeZero N]` (theorem): The supplied proof does not need this instance: GammaH, gamma0Units, mem_GammaH_iff, Gamma0Map and ZMod.unitsMap are defined without nonzero assumptions. Moreover, the remaining hypothesis NeZero (N * ℓ) implies N ≠ 0. Both nonzero hypotheses can actually be deleted together.
- `[NeZero (N * ℓ)]` (theorem): The same proof works without this instance. ZMod.unitsMap is Units.map of ZMod.castHom, requiring only divisibility, and the proof uses preservation of integer casts and zero, not finiteness or surjectivity. The newly permitted case ℓ = 0 works too: ZMod 0 = ℤ, Gamma0 0 means the lower-left entry is exactly zero, and the same cast and unit calculations apply. Both nonzero hypotheses can be deleted together, also allowing N = 0.

### [`TateCurve.pointX_inv_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_TateCurve_XMultStructure.lean#L171-L175) — `flt-anthropic-0057`

Snippet: `samples/flt-anthropic/flt-anthropic-0057.lean`

- `(hq0 : q ≠ 0)` (theorem): Split on q = 0; otherwise use the existing proof. Set z = u * v⁻¹. When q = 0, compare xTerm 0 z⁻¹ (-n) with xTerm 0 z n: for n ≠ 0 both vanish by zero_zpow and xfun_zero; for n = 0 use xfun_inv, with z ≠ 0 from hu0 and hv0 and z ≠ 1 from hdiv 0. Reindex using tsum_comp_neg; the identical s₁ correction cancels.
- `(hu0 : u ≠ 0)` (theorem): Split on u = 0. In that case both u⁻¹ * v and u * v⁻¹ are zero, so the conclusion is reflexive after simplification. Otherwise the existing proof applies.
- `(hv0 : v ≠ 0)` (theorem): Split on v = 0. In that case both arguments of pointX are zero, using inv_zero, so simplification proves the equality. Otherwise use the existing proof.
- `(hdiv : OffLattice q (u * v⁻¹))` (theorem): The source proof of pointX_inv only uses this condition in xfun_inv. Extend that rational identity to w = 1 separately: inv_one makes it reflexive (and xfun 1 = 0 under division-by-zero conventions). Apply the extended identity to each nonzero q^n * (u * v⁻¹), then repeat the source proof using tsum_comp_neg and tsum_congr. Neither lemma requires summability.
- `[CompleteSpace K]` (variable): The definitions pointX, s₁ and coeffSum do not retain this unused instance. Replace the call to pointX_inv by its source proof: establish the termwise identity using xfun_inv, then apply tsum_comp_neg and tsum_congr. These steps require no completeness or convergence assumption, including for nonsummable series.
- `[IsUltrametricDist K]` (variable): OffLattice and the definitions underlying pointX do not retain this instance. Reproduce the source proof of pointX_inv, replacing xfun_inv with its elementary field proof: unfold xfun, clear the nonzero denominators with div_eq_div_iff, and use the same linear_combination argument found in its source. The required denominator conditions follow from hq0, hu0, hv0 and hdiv. Finish with tsum_comp_neg and tsum_congr; no ultrametric property or convergence is needed.

### [`P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.Nat.not_mem_placesOf_of_mem_placesOf_of_coprime`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.lean#L72-L74) — `flt-anthropic-0058`

Snippet: `samples/flt-anthropic/flt-anthropic-0058.lean`

- `(hℓ : ℓ ≠ 0)` (theorem): Split on ℓ = 0. In the zero case, placesOf 0 = ∅ by its definition and Ideal.span_singleton_zero, contradicting hv. Otherwise use the original proof. Both nonzero hypotheses can also be deleted together.
- `(hℓ' : ℓ' ≠ 0)` (theorem): Split on ℓ' = 0. In the zero case, placesOf 0 = ∅ by its definition and Ideal.span_singleton_zero, so the conclusion holds immediately. Otherwise use the original proof. Both nonzero hypotheses can also be deleted together.

### [`P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.lean#L843-L876) — `flt-anthropic-0059`

Snippet: `samples/flt-anthropic/flt-anthropic-0059.lean`

- `(hn : ‖n‖ = 1)` (theorem): Write V for the valuations and d for the completion degree. By v_eq_exp_of_norm_eq_zpow, hm gives V(1-n)=exp(-m)≤1; Valuation.map_sub then gives V(n)≤1. If V(n)=1, Valued.toNormedField.norm_eq_one_iff supplies hn and the existing proof applies. Otherwise V(n)<1, so Valuation.map_sub_eq_of_lt_left gives V(1-n)=1, forcing m=0. The helpers exists_eq_algebraMap_mul_unit, v_theta_eq_one and v_algebraMap show that every θ^i preserves valuation: decompose each nonzero element as a base-field scalar times a valuation-one element. Applying valuation to hc therefore gives V(c)^d=V(n)<1. Since hprime.pos gives d>0, V(c)<1. Consequently Valuation.map_sub_eq_of_lt_left gives V(θ x-c*x)=V(x) for every nonzero x; zero is immediate. Thus the first comap in the conclusion equals the integer subgroup. The second comap contains that subgroup, by pi_mem and pis_eq. Their intersection is therefore the integer subgroup, and AddSubgroup.relIndex_self gives 1, equal to the right side since m=0. This also covers n=0 and c=0.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L610-L612) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- `[CharZero L]` (variable): The existing proof works unchanged without this instance: algebraMap_laurentSeries_eq_single assumes only [Field L], and HahnSeries.C_apply requires no characteristic assumption. Both sides equal HahnSeries.single 0 c in every characteristic, including when c = 0. Use omit [NeZero m] [CharZero L] in.

### [`P2MW.S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition.KSpec.cube_eq_neg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_so3Triple_typeOne_ker_identities_and_decomposition.lean#L356-L585) — `flt-anthropic-0063`

Snippet: `samples/flt-anthropic/flt-anthropic-0063.lean`

- `(hF₁ : ∀ f ∈ F, J₁ f ∈ F)` (theorem): Recover it using h23: J₁ f = J₂ (J₃ f) - J₃ (J₂ f). Both terms belong to F by hF₂ and hF₃, so Submodule.sub_mem applies. Then retain the original proof. This also works when F = ⊥.
- `(hF₂ : ∀ f ∈ F, J₂ f ∈ F)` (theorem): Recover it using h31: J₂ f = J₃ (J₁ f) - J₁ (J₃ f). Membership follows from hF₁, hF₃ and Submodule.sub_mem. The original proof then applies, including for F = ⊥.
- `(hF₃ : ∀ f ∈ F, J₃ f ∈ F)` (theorem): Recover it using h12: J₃ f = J₁ (J₂ f) - J₂ (J₁ f). Membership follows from hF₁, hF₂ and Submodule.sub_mem. The original proof then applies, including for F = ⊥. Each invariance deletion described here retains the other two invariance hypotheses.
- `(hskew₁ : ∀ x ∈ F, ∀ y ∈ F, B (J₁ x) y = -B x (J₁ y))` (theorem): Derive the existing hBsub and hBsub' formulas from hlin and hsymm. Using h23 and the other two skew identities gives B(J₁ x,y) = -B(J₃ x,J₂ y) + B(J₂ x,J₃ y) = B(x,J₃(J₂ y)) - B(x,J₂(J₃ y)) = -B(x,J₁ y). Invariance supplies all required memberships. Insert this recovered hypothesis before continuing the original proof. No nonzero assumption is needed.
- `(hskew₂ : ∀ x ∈ F, ∀ y ∈ F, B (J₂ x) y = -B x (J₂ y))` (theorem): Using hBsub and hBsub' (derived from hlin and hsymm), expand h31 and apply hskew₃ and hskew₁ twice: B(J₂ x,y) = B(x,J₁(J₃ y)) - B(x,J₃(J₁ y)) = -B(x,J₂ y). Invariance supplies the memberships, so the original proof can continue unchanged. This includes zero vectors and the trivial module.
- `(hskew₃ : ∀ x ∈ F, ∀ y ∈ F, B (J₃ x) y = -B x (J₃ y))` (theorem): Using hBsub and hBsub' (derived from hlin and hsymm), expand h12 and apply hskew₁ and hskew₂ twice: B(J₃ x,y) = B(x,J₂(J₁ y)) - B(x,J₁(J₂ y)) = -B(x,J₃ y). Invariance supplies the memberships. The original proof then applies without any nonzero restriction. Each skew deletion described here retains the other two skew hypotheses.

### [`P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.W8O.ramificationIndex_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.lean#L169-L198) — `flt-anthropic-0064`

Snippet: `samples/flt-anthropic/flt-anthropic-0064.lean`

- `[FiniteDimensional M E]` (variable): Avoid theta and use hrange directly: writing N = p^r > 0, RingHom.mem_fieldRange identifies the image of M with the Nth powers in E. A uniformizer π therefore has π^N = algebraMap M E m, giving ramificationIndex ≤ N by Place.ramificationIndex_le_ord and ord_npow. Conversely, Place.exists_ord_eq_ramificationIndex and Place.ramificationIndex_pos give a positive minimal order e; hrange writes its witnessing image as x^N, so e = N*w.ord x ≥ N. These two lemmas require only integrality, supplied by the remaining IsPurelyInseparable instance. This works for infinite-dimensional extensions and for r = 0; the uniformizer and its positive powers are nonzero.
- `[IsPurelyInseparable M E]` (variable): Recover this instance from hrange. For every x : E, hrange and RingHom.mem_fieldRange imply x^(p^r) belongs to (algebraMap M E).range. With ExpChar M p supplied by the remaining prime and characteristic assumptions, isPurelyInseparable_iff_pow_mem establishes IsPurelyInseparable M E, choosing exponent r for every x. Then the original proof applies. This includes x = 0 and r = 0.
- `[CharP M p]` (variable): Recover it locally using (algebraMap M E).charP (algebraMap M E).injective p, an application of RingHom.charP using the remaining CharP E p. The original proof then applies unchanged. Algebra maps between fields are injective, so no trivial-field exception arises.

### [`P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.lean#L2414-L2438) — `flt-anthropic-0066`

Snippet: `samples/flt-anthropic/flt-anthropic-0066.lean`

- `(ha2 : a ^ (q ^ 2) = a)` (theorem): The existing proof works unchanged: ha2 is never used, and ModularCurve.C4b.core has no corresponding hypothesis. No restriction on a beyond the remaining hypotheses is needed.
- `(h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)` (theorem): Split on whether the reduced Laurent series is zero. In the nonzero case, use the existing proof. In the zero case, Subtype.ext identifies the element in the conclusion with zero, and AlgebraicCurve.Place.ord_zero proves the conclusion. This lemma explicitly states ord 0 = 0 in Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean.

### [`P2MW.S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_PolarisedAbelianScheme_exists_fg_subalgebra_abelianScheme_closedImmersionBySections_comp_eq_comp_of_isIso_of_pullback_pol_iso.lean#L607-L672) — `flt-anthropic-0068`

Snippet: `samples/flt-anthropic/flt-anthropic-0068.lean`

- `(hσiso : IsIso σ.1)` (theorem): This follows from hpol and the checked fields of PolarisedAbelianScheme. Since Spec k has one point, hpol gives a global isomorphism σ* u.pol ≅ u.pol. The definitions of pol_isInvertible and pol_veryAmple make u.pol a very ample line bundle. Also, u.bundle makes u.A smooth, proper and connected over k, hence integral and normal. The proper endomorphism σ.1 is quasi-finite: on any positive-dimensional proper fibre its pullback line bundle would be both ample and trivial, which is impossible. Thus it is finite, and dimension forces it to be surjective. Comparing leading coefficients of Hilbert polynomials using σ* u.pol ≅ u.pol gives deg σ = 1. A finite birational morphism onto a normal scheme is an isomorphism. This also covers dimension zero, where the Hilbert polynomial is a positive constant; emptiness is excluded by the group-law unit section. Derive hσiso this way, then use the existing proof unchanged.

### [`P2MW.S_CohCarrier_isEis_kernel_pair_of_prime.CohCarrier.IsEisKernelPairPrime.exists_crt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_isEis_kernel_pair_of_prime.lean#L359-L443) — `flt-anthropic-0072`

Snippet: `samples/flt-anthropic/flt-anthropic-0072.lean`

- `[NeZero P]` (theorem): mapN and mapN_eq_iff require no nonzero assumption. Split on P = 0. In that case Nat.coprime_zero_left gives M₁ = 1; choose g₁ = g. The first equality is reflexive, and the second follows from mapN_eq_iff since 1 divides every integer. Otherwise install NeZero P and use the existing proof. Both nonzero hypotheses can also be removed simultaneously.
- `[NeZero M₁]` (theorem): Split on M₁ = 0. Nat.coprime_zero_right then gives P = 1; choose g₁ = 1. The second equality follows because mapN is a monoid homomorphism, and the first follows from mapN_eq_iff since 1 divides every integer. Otherwise install NeZero M₁ and use the existing proof. Neither mapN nor the conclusion requires this instance; both nonzero hypotheses can also be removed simultaneously.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart_of_eq_three.B3Ends.sc_pow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_ends_of_affineChart_of_eq_three.lean#L92-L93) — `flt-anthropic-0076`

Snippet: `samples/flt-anthropic/flt-anthropic-0076.lean`

- `[IsDomain (CoordRing q k)]` (variable): The same proof works with this instance omitted. `drinfeldFunctionField q k` is `FractionRing (CoordRing q k)`, defined as localization at the non-zero-divisors for any commutative ring; its ring and algebra structures do not require a domain. Neither `sc` nor `scalarOf_pow_of_mem` needs this hypothesis. The proof merely maps the scalar's power identity through an algebra map, so zero-divisors or even a trivial target ring cause no exception.

### [`P2MW.S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd.LevelRaisingCornerDvdSol.heckeT_wL_eq_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_levelRaisingComb_mem_cornerSubmodule_of_prime_of_dvd.lean#L429-L433) — `flt-anthropic-0077`

Snippet: `samples/flt-anthropic/flt-anthropic-0077.lean`

- `[NeZero N]` (variable): The statement's definitions do not require this instance. Split on N = 0; the nonzero case uses the existing proof. At N = 0, iDeg' with parameter 1 is the identity. Moreover, T(iDeg' q φ) = q • φ: use heckeT_card_smul_impl from S_CohCarrier_heckeT_iDeg_q_eq_smul.lean. Its compatibility condition follows directly because conjLowerMat q cancels conjUpperMat q, using q ≠ 0 and divisibility of the upper-right entry. The quotient cardinal is q by that file's IharaMintIdx.natCard_rightQuot, which requires only [NeZero q] and q ∣ M, and therefore applies at M = 0. These facts give T(wL v) = q • T(v) - q • T(v) = 0. Thus the zero-level case holds too, for every coefficient ring, including the trivial ring.

### [`P2MW.S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.lean#L36-L71) — `flt-anthropic-0083`

Snippet: `samples/flt-anthropic/flt-anthropic-0083.lean`

- `[NeZero N]` (theorem): The existing proof works unchanged without this instance. The definitions of x1FunctionField, x1FunctionFieldBar, JOne, and their Galois action are valid for every natural N, including N = 0. arithmeticGalois is defined for any intermediate field, and the pairing and inertia lemmas used impose no nonzero-level condition. Thus the zero-level case is covered by exactly the same argument.

### [`P2MW.S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.Loc4Sol.residual_isEquiv_point`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.lean#L165-L200) — `flt-anthropic-0088`

Snippet: `samples/flt-anthropic/flt-anthropic-0088.lean`

- `(hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)` (theorem): Apply GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq with exceptional finset S ∪ N.primeFactors instead of S. Outside this union, the original Frobenius calculation applies: Nat.mem_primeFactors and NeZero.ne N give ¬ ℓ ∣ N. The remaining proof is unchanged. This also works for S empty and N = 1; N = 0 remains excluded.
- `(habs : ρbar.IsAbsolutelyIrreducible)` (theorem): The proof obtains hall without either irreducibility assumption. Apply ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq to habs' and hall to obtain absolute irreducibility of ρbar.baseChangeAlong φk, then use the original equivalence lemma. This works over every residue field, including characteristic 2. Either habs or habs' can be deleted individually, but not both.
- `(habs' : ρ'.residual.IsAbsolutelyIrreducible)` (theorem): Obtain absolute irreducibility of ρbar.baseChangeAlong φk using habs.baseChangeAlong φk. Transfer it to ρ'.residual using ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq and the pointwise symmetry of hall, then finish with the original equivalence lemma. No characteristic restriction is needed. Either habs or habs' can be deleted individually, but not both.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.K45VolB3.iterate_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.lean#L218-L220) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- `[NumberField L]` (variable): The definition of AutomorphicForm.sigmaTensor requires only [Field K], [Field L], [Algebra K L], and a commutative K-algebra A. The local sigmaTensor_pow lemma has the same requirements. Taking A = Kv uses [NumberField K], not [NumberField L], so the existing rewrite proof works unchanged after omitting [NumberField L]. This is multiplicativity of an iterated ring homomorphism, valid for every i, including i = 0, and all x and y, including zero.

### [`P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD.pairF_res_cores_normal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_index_Gamma_four.lean#L5591-L5659) — `flt-anthropic-0095`

Snippet: `samples/flt-anthropic/flt-anthropic-0095.lean`

- `[Γ'.FiniteIndex]` (theorem): It follows from [Φ.FiniteIndex] and hΦΓ by Subgroup.finiteIndex_of_le. The conclusion needs no Γ'.FiniteIndex instance; after deleting this binder, introduce `letI := Subgroup.finiteIndex_of_le hΦΓ` and retain the proof. This implication has no additional nontriviality assumptions.
- `(hΦ1 : (-1 : SL(2, ℤ)) ∉ Φ)` (theorem): This follows from [IsFreeGroup Φ]. IsFreeGroup.toFreeGroup identifies Φ with a free group, whose HasUniqueRoots instance is proved in Mathlib/GroupTheory/FreeGroup/CyclicallyReduced.lean. If -1 belonged to Φ, its image under this equivalence would square to 1, hence equal 1. Injectivity would imply -1 = 1 in SL(2, ℤ), contradicted by their (0,0) matrix entries. Derive hΦ1 this way and retain the existing proof. The argument also covers a trivial free group and is independent of R.

### [`P2MW.S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.lean#L99-L202) — `flt-anthropic-0099`

Snippet: `samples/flt-anthropic/flt-anthropic-0099.lean`

- `[Fact p.Prime]` (theorem): Neither the remaining statement's definitions nor the proof require primality. The finite-avoidance argument on Mdl₁ works unchanged, including in characteristic zero.
- `[NeZero M]` (theorem): IntegralWeightOneForm and igusaFunctionFieldX1C require no nonzero-level instance, and the proof does not use it. Moreover, the retained hM excludes M = 0.
- `(hM : 5 ≤ M)` (theorem): Unused by the proof and subsequent binders. For every remaining level, the supplied curve model provides all geometric properties needed by the same argument.
- `(hpM : ¬ p ∣ M)` (theorem): Unused by the statement's subsequent binders and by the proof. The proof works unchanged when p divides M.
- `[IsCyclotomicExtension {p} ℚ L]` (theorem): The remaining definitions need the retained field and rational algebra structures, not cyclotomicity. No proof step uses this instance.
- `(hζ : IsPrimitiveRoot ζ p)` (theorem): No subsequent binder or proof step uses hζ. The same geometric proof works for arbitrary ζ satisfying the remaining assumptions.
- `(hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))` (theorem): Unused throughout the proof and subsequent binders. The argument uses the supplied two-chart morphisms and curve model directly, without identifying K with this base change.
- `[IsFractionRing A L]` (theorem): TwoChart.modelTo and TwoChart.ιFin require only the commutative ring, field, algebra and nonzero-j structures retained here. Neither subsequent binders nor the proof require this fraction-ring instance.
- `(hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)` (theorem): Unused by subsequent binders and by the proof. The argument only needs the supplied special-fibre morphisms, not this arithmetic condition.
- `(hζA : ∃ z : A, algebraMap A L z = ζ)` (theorem): Unused by subsequent binders and by the proof; no integral lift of ζ is needed.
- `[IsScalarTower A L ↥K]` (theorem): The two-chart construction uses the explicitly retained Algebra A ↥K, without compatibility with L. No subsequent binder or proof step requires this tower instance.
- `(hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)` (theorem): Unused by the proof and subsequent binders. The required nonzero-j instance remains explicitly assumed, so the proof works for arbitrary such j.
- `[CharP k p]` (theorem): IntegralWeightOneForm and igusaFunctionFieldX1C require only Field k. The curve-model lemmas and Pic0.mem_closure_mk_single_sub_single_of_notMem used in the proof are characteristic-independent.
- `[IsProper c₁]` (theorem): The proof uses properness of Mdl₁.toBase supplied by CurveModel, not this instance. SchemeHomOver requires no properness assumption, so the statement and proof remain valid.
- `[SmoothOfRelativeDimension 1 c₁]` (theorem): The required smoothness belongs to Mdl₁.toBase and is supplied by CurveModel. No remaining binder or proof step needs this separate instance.
- `[GeometricallyIntegral c₁]` (theorem): The proof obtains integrality from Mdl₁ itself. Its point equivalences and finite-complement argument require no geometric-integrality instance for c₁.
- `[IsProper c₂]` (theorem): Unused. C₂ enters the proof only through the pullback's point set, whose finiteness follows from hn and hn0; properness is unnecessary.
- `[SmoothOfRelativeDimension 1 c₂]` (theorem): Unused. The proof needs only the pullback's finiteness from hn and hn0, not smoothness of c₂.
- `[GeometricallyIntegral c₂]` (theorem): Unused. Finiteness of the excluded crossing set follows directly from hn and hn0, independently of integrality or nonemptiness of C₂.
- `[IsClosedImmersion i₁.1]` (theorem): Neither SchemeHomOver nor the pullback requires this property. The proof uses only i₁ as a morphism; its injectivity argument concerns e₁, not i₁.
- `[IsClosedImmersion i₂.1]` (theorem): The proof uses only the range of the pullback projection and bounds it using hn and hn0. No closed-immersion property is needed.
- `(hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)` (theorem): Unused. The proof operates on Mdl₁ and its nonempty open U; it never requires the two morphisms to cover the special fibre.
- `(hred : IsReduced (pullback i₁.1 i₂.1))` (theorem): Unused. Only the underlying pullback point set matters, and hn with hn0 already proves it finite. Nonreduced structure does not affect the argument.

### [`P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.R4GC.qC_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.lean#L1440-L1442) — `flt-anthropic-0104`

Snippet: `samples/flt-anthropic/flt-anthropic-0104.lean`

- `[NeZero m]` (variable): The definitions of Γ, GH and levelH require no nonzero assumption. Under `omit [NeZero m] in`, prove locally that 1 belongs to `(Γ m M').strictPeriods` by replaying `one_mem_strictPeriods`: use `ModularCurve.translation_mem_GammaH`, then `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem` and `AddSubgroup.mem_zmultiples`. These lemmas work for every level, including m = 0 and M' = 0. The original proof then works unchanged with this local period fact: `ModularForm.qExpansion_eq_zero_iff` and `HahnSeries.ofPowerSeries_injective` require no nonzero level.

### [`P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.R3M4Torus.ι₀_root`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.lean#L48-L49) — `flt-anthropic-0111`

Snippet: `samples/flt-anthropic/flt-anthropic-0111.lean`

- `[Fact (Irreducible γ₀.charpoly)]` (variable): The definitions of E and ι₀ do not require irreducibility: AdjoinRoot has its algebra structure unconditionally, and ι₀ is defined using Cayley–Hamilton. After omitting this instance, unfold AdjoinRoot.root and ι₀; the quotient lift reduces definitionally to Polynomial.aeval γ₀ Polynomial.X, so Polynomial.aeval_X proves the equality. This works for every γ₀, including zero matrices and matrices with reducible characteristic polynomial.

### [`P2MW.S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.lean#L32-L223) — `flt-anthropic-0121`

Snippet: `samples/flt-anthropic/flt-anthropic-0121.lean`

- `(hpS : p ∈ S)` (theorem): Recover it as `hNS p (Fact.out : p.Prime) hpN`. The proof already constructs this as `hpinS`; pass that instead of `hpS` to the jointly-injective-points theorem. This works for every case allowed by the remaining hypotheses.
- `(hNp : ¬ p ^ 2 ∣ N)` (theorem): Recover it by `fun h => hθ'U (hU0 p Fact.out hpN (hNS₀ p Fact.out hpN) h)` and use this in the existing proof. Thus the excluded case contradicts the remaining hypotheses directly.
- `(hTp : ∀ (hpN : ¬ p ∣ N) (hpS₀ : p ∉ (↑S₀ : Set ℕ)), ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p → ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p → ∀ E : (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)) →ₗ[ResidueField 𝒪] (ρbar.V ⧸ ⨆ τ ∈ P.inertiaSubgroupIn ℚ, LinearMap.range (ρbar.ρ τ - 1)), (∀ v : ρbar.V, E (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρbar.ρ σ v)) → θ' (CuspForm.heckeAlgebra.T (Fact.out : p.Prime) hpN hpS₀) = LinearMap.trace (ResidueField 𝒪) _ E)` (theorem): Its first premise contradicts the retained outer `hpN : p ∣ N`. Replace its use in the jointly-injective-points theorem by `fun hnot => False.elim (hnot hpN)`. No Frobenius or quotient-space cases need additional assumptions.
- `(hθ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), θ t = θ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))` (theorem): Neither subsequent binders nor the conclusion depend on `hθ`, and the proof never uses it. The compatibility actually used is `hΨ`, which remains available. The existing proof therefore works unchanged, including all degenerate cases.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.M4aD2Skeleton.zetaIntegral_eq_setIntegral_theta'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.lean#L6363-L6392) — `flt-anthropic-0122`

Snippet: `samples/flt-anthropic/flt-anthropic-0122.lean`

- `(hD'm : MeasurableSet D')` (theorem): The unfolding lemma requires only hD', not hD'm. The remaining integrands agree at every x by the existing hterm argument. Replace setIntegral_congr_fun hD'm with MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ...), applied under ν.restrict D'. This also works for empty or nonmeasurable D'.
- `[BorelSpace (AdeleRing (𝓞 F) F)]` (theorem): This instance is needed only when invoking ideleNorm_mul_principal. Prove that step locally with MeasurableSpace (AdeleRing (𝓞 F) F) := borel _ and BorelSpace := ⟨rfl⟩. Its conclusion, ideleNorm, schwartzBruhat, and ThetaSum do not depend on the measurable structure on the adele ring. The integration measure and measurable structure on its units remain unchanged, so the rest of the proof works without this hypothesis, with no exceptional cases.

### [`P2MW.S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.NumberField.AdelicFourier.GodementSiegelEstimate.real_bound`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.lean#L337-L423) — `flt-anthropic-0123`

Snippet: `samples/flt-anthropic/flt-anthropic-0123.lean`

- `(hC : 0 ≤ C)` (theorem): Split on 0 ≤ C. In that case use the existing proof. Otherwise C ≤ 0; choose B = 0. Since r ≥ 1 and α, δ > 0, their product inverses and all natural powers are nonnegative, including when N = 0. Thus both minima and every factor multiplying C are nonnegative. Repeated use of mul_nonpos_of_nonpos_of_nonneg gives left-hand side ≤ 0, while the right-hand side is zero. This also handles C = 0.

### [`P2MW.S_TateCurve_ks17_D3_exports.TateCurve.sum_mul_Fz_Fz_eq_sum_lines_nat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_ks17_D3_exports.lean#L108-L111) — `flt-anthropic-0124`

Snippet: `samples/flt-anthropic/flt-anthropic-0124.lean`

- `[IsUltrametricDist K]` (theorem): The proof in S_TateCurve_ks17_C3_exports.lean:230–244 works without this instance: apply TateCurve.sum_mul_Fz_eq_sum_lines_nat twice and rearrange finite sums using ring. That lemma, defined in Def_TateCurve_DefectLines.lean:1349, requires only NontriviallyNormedField K. Fz itself requires only Field K. Empty sums cause no issue; when N = 0 the bounds force both indices to zero, and Fz_zero makes every summand zero, including when u or v is zero. Both reported instances can be deleted together.
- `[CompleteSpace K]` (theorem): No completeness is needed for this finite-sum identity. Reuse the proof in S_TateCurve_ks17_C3_exports.lean:230–244, applying TateCurve.sum_mul_Fz_eq_sum_lines_nat twice; its definition in Def_TateCurve_DefectLines.lean:1349 has no completeness assumption. Fz requires only Field K, and Fz_zero handles zero indices for arbitrary u and v. Thus empty S and N = 0 are covered as well. Both reported instances can be deleted together.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal.Ψ₂Sq_𝓦p_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L273-L277) — `flt-anthropic-0125`

Snippet: `samples/flt-anthropic/flt-anthropic-0125.lean`

- `(hp2 : p ≠ 2)` (theorem): Use coefficient 2 instead of coefficient 3. By the definitions of Ψ₂Sq, b₂ and 𝓦p, this coefficient is (MvPolynomial.X 0)^2 + 4 * MvPolynomial.X 1. If Ψ₂Sq were zero, this coefficient would vanish. Applying MvPolynomial.eval ![1, 0, 0, 0, 0] and simplifying with MvPolynomial.eval_X gives 1 = 0 in ZMod p, contradicting nontriviality from p.Prime. This argument also works for p = 2, so hp2 can be deleted.

### [`P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.KcSemiLocalIwasawaHaar.mem_K_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean#L1008-L1009) — `flt-anthropic-0126`

Snippet: `samples/flt-anthropic/flt-anthropic-0126.lean`

- `[NumberField L]` (variable): After `omit [NumberField L] in`, the unchanged statement still elaborates and the proof remains `Iff.rfl`. `semiLocalIntegralSet` unfolds to `integralUnitsSet (semiLocalIntegers K L v)`, whose defining predicate is exactly the right-hand side. Neither definition requires `[NumberField L]`; the existing `one_mem_semiLocalIntegralSet` also explicitly omits it. This is a definitional equivalence, with no exceptional or degenerate cases.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.AlgebraicCurve.HolRingFGAux.exists_fin_generators`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.lean#L590-L610) — `flt-anthropic-0132`

Snippet: `samples/flt-anthropic/flt-anthropic-0132.lean`

- `(hN : N.Nonempty)` (theorem): Split on whether N is nonempty, using the existing proof in that case. If N = ∅, choose n = 0 and z = Fin.elim0. Every f regular at all places belongs to LSpace 0, including f = 0. Obtain a transcendental x and FiniteDimensional k⟮x⟯ K from IsCurveOver.exists_separating_transcendental. The library lemma AlgebraicCurve.constantsAreBase_of_isAlgClosed_of_transcendental then identifies LSpace 0 with the range of Algebra.linearMap k K. Thus f is a base-field constant and belongs to Algebra.adjoin k ∅ by Algebra.adjoin_empty and Algebra.mem_bot. The generators' regularity condition is vacuous.

### [`P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.MapsDvdSol.opFamily_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.lean#L343-L365) — `flt-anthropic-0134`

Snippet: `samples/flt-anthropic/flt-anthropic-0134.lean`

- `[IsDomain 𝒪]` (variable): The same proof works without this instance. opFamily requires only CommRing 𝒪 and NeZero N; diamondL_top_eq_one has the same requirements, and heckeT_comm_of_prime works with arbitrary additive commutative coefficients. No cancellation or absence of zero divisors is used.
- `[CharZero 𝒪]` (variable): The same proof works in positive characteristic: opFamily and diamondL_top_eq_one require only CommRing 𝒪 and NeZero N, while heckeT_comm_of_prime requires only additive commutative coefficients. The primality and coprimality arguments concern natural-number indices, not their images in 𝒪.
- `[IsLocalRing 𝒪]` (variable): Neither the statement's definitions nor the proof's lemmas require locality. The same proof works for any commutative coefficient ring. All three reported instances can also be omitted simultaneously; even the zero ring is harmless, since its coefficient homomorphisms and endomorphisms are unique.

### [`P2MW.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.ModularCurve.map_eval₂_aeval_toRingHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.lean#L18-L24) — `flt-anthropic-0137`

Snippet: `samples/flt-anthropic/flt-anthropic-0137.lean`

- `[Algebra ℤ A]` (theorem): Deleting this binder leaves aeval well-defined: Ring.toIntAlgebra supplies Algebra ℤ A from CommRing A. The existing proof works unchanged with this canonical instance. Mathlib's int_algebra_subsingleton confirms that the integer algebra structure is unique. No nontriviality assumption is needed, so trivial rings are covered. Both algebra binders can also be deleted together.
- `[Algebra ℤ B]` (theorem): Ring.toIntAlgebra supplies this instance from CommRing B, so deleting the binder requires no statement or proof changes. The proof still uses hom_eval₂ and Polynomial.ringHom_ext', with RingHom.ext_int identifying the coefficient maps and aeval_X handling X. These lemmas apply to trivial rings too. Both algebra binders can also be deleted together.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.C2Count.natCard_finPts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.lean#L214-L257) — `flt-anthropic-0143`

Snippet: `samples/flt-anthropic/flt-anthropic-0143.lean`

- `(hm : 0 < m)` (theorem): The existing lemma `not_dvd_of_coprime hmp` gives `hpm : ¬ p ∣ m`. Hence m ≠ 0, since `Nat.dvd_zero p` would contradict hpm when m = 0. Recover hm using `Nat.pos_of_ne_zero` and then use the original proof unchanged. Thus the zero case is already excluded by the remaining hypotheses.

### [`P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve.SmoothedFundamentalProof.finite_support_smul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.lean#L435-L442) — `flt-anthropic-0144`

Snippet: `samples/flt-anthropic/flt-anthropic-0144.lean`

- `[Γ.FiniteIndex]` (variable): The definition of smoothedFundamental uses finsum and requires no finite-index instance. Set f δ := puCut T (mob δ τ); hasFiniteSupport_puCut_mob proves its support finite for every T and τ. Pull this support back along cosetEquiv Γ : (SL(2, ℤ) ⧸ Γ) × Γ ≃ SL(2, ℤ), then take its finite image under Prod.snd. The claimed support is contained in this image: using coe_smul and mob_mob, its value at γ is ∑ᶠ q, f (q.out * γ); if nonzero, some summand is nonzero, since otherwise finsum_eq_zero_of_forall_eq_zero applies. This proof works for arbitrary subgroups, infinite quotients, and empty supports.

### [`P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.AlgebraicCurve.BaseChangeTwo.lhs_eq_rhs_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.lean#L327-L359) — `flt-anthropic-0149`

Snippet: `samples/flt-anthropic/flt-anthropic-0149.lean`

- `(hg : g ≠ 0)` (theorem): Split on g = 0. In the nonzero case, use the existing proof. When g = 0, Place.ord_zero (Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean) makes hD imply D = 0 by Finsupp extensionality, including when the place type is empty. Since lhs and rhs are additive homomorphisms, both send D = 0 to zero.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.P2mFlatIsog.ringKrullDim_stalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.lean#L246-L300) — `flt-anthropic-0150`

Snippet: `samples/flt-anthropic/flt-anthropic-0150.lean`

- `[LocallyOfFiniteType fX]` (theorem): Replace the proof's use of exists_algebra_finiteType fX by exists_algebra_finiteType (h ≫ fY). IsFinite h supplies LocallyOfFiniteType h, and locallyOfFiniteType_comp supplies LocallyOfFiniteType (h ≫ fY). Everything else is unchanged; no compatibility between fX, fY and h is required. The point x ensures the affine neighborhoods used are nonempty. Each finite-type hypothesis is independently deletable, but in general they cannot both be dropped.
- `[LocallyOfFiniteType fY]` (theorem): Retain the affine reduction, writing B → A for its integral injection and P over Q for the selected primes. Only A needs to be finite type over K. Every prime P' over Q has the same height as P: the integral injections B/Q → A/P' and B/Q → A/P give equal quotient dimensions by ringKrullDim_eq_of_isIntegral_of_injective, and Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType applied in A gives equal heights. Lift any finite prime chain ending at Q using exists_ltSeries_comap_eq_last; its lift ends at such a P', so height Q ≤ height P. Conversely, contraction preserves strict prime chains under an integral map, as in the existing ringKrullDim_eq_of_isIntegral_of_injective proof. Thus the heights agree without finite type for B. All dimensions used in cancellation are finite because A and its prime quotients are finite-type domains over K; x excludes empty neighborhoods. The other finite-type hypothesis is retained; in general both cannot be dropped.
- `[IsIntegral Y]` (theorem): On the chosen affine neighborhoods, let φ : B → A and I = ker φ. Surjectivity of h implies every prime of B contains I. Replace B by B/I: it is a domain since RingHom.kerLift_injective embeds it into the domain A, remains finite type over K, and its map to A is integral by RingHom.IsIntegral.kerLift. Apply the existing height_comap_eq to this injection. Ideal.primeSpectrumQuotientOrderIsoZeroLocus identifies Spec(B/I) with all of Spec(B), since every prime contains I, so the corresponding prime heights are unchanged. The existing stalk-localization argument finishes. This explicitly handles nonreduced targets; x makes the neighborhoods and quotient domain nontrivial.

### [`P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.NumberTheory.kw_hjoint_normBasis_liftHom_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.lean#L674-L685) — `flt-anthropic-0151`

Snippet: `samples/flt-anthropic/flt-anthropic-0151.lean`

- `[CharZero F]` (variable): The definition kw_hjoint_normBasis uses only field operations and ring identities, so it does not require CharZero. Mathlib's Basis.liftHom likewise requires only the ring/algebra structures. After `omit [CharZero F] in`, the same proof works: unfold the lift, check the four matrix entries using Matrix.algebraMap_matrix_apply, and close with ring. These identities hold in every characteristic, including characteristic two, and require no nonzero conditions on a, b, u, v, or z.

### [`P2MW.S_CuspidalType_sum_character_mul_character_inv.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspidalType_sum_character_mul_character_inv.lean#L10-L30) — `flt-anthropic-0154`

Snippet: `samples/flt-anthropic/flt-anthropic-0154.lean`

- `[CharZero K]` (theorem): Split on whether (Nat.card (GL2 q) : K) is zero. If nonzero, the existing orthogonality proof works unchanged. If zero, put τ = Representation.linHom ρ ρ and T = ∑ g, τ g. Reindexing the double sum gives T² = Nat.card (GL2 q) • T = 0. Hence LinearMap.isNilpotent_trace_of_isNilpotent implies trace T = 0, since K is a field. By linearity of trace and Representation.char_linHom, trace T is the required character sum. Thus both sides vanish in the previously excluded characteristics.
- `[FiniteDimensional K V]` (theorem): Representation.character is defined using LinearMap.trace without requiring finite dimensionality, so the statement still elaborates. The proof constructs IsIrreducible ρ without this hypothesis. For finite GL2 q, Representation.IsIrreducible provides finite dimensionality of ρ.asModule, transferred to V by ρ.asModuleEquiv; Representation.char_orthonormal already performs this transfer internally. The remaining proof therefore works without the binder. Nontriviality remains assumed, and irreducibility rules out any additional infinite-dimensional cases.

### [`P2MW.S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.K51A1.retr_tmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.lean#L38-L40) — `flt-anthropic-0160`

Snippet: `samples/flt-anthropic/flt-anthropic-0160.lean`

- `[FiniteDimensional K L]` (variable): The definition of retr uses no finite-dimensionality assumption. After omitting this instance, the existing proof works unchanged: LinearMap.rTensor_tmul and TensorProduct.lid_tmul give the equality for arbitrary l and a, including zero.
- `[IsTopologicalRing A]` (variable): Neither retr nor the two tensor-product identities used in the proof require continuity of the ring operations. Omitting this instance leaves the statement and proof valid unchanged, including when A is the trivial ring.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.R4ODGlue.eq_of_proj_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.lean#L415-L421) — `flt-anthropic-0167`

Snippet: `samples/flt-anthropic/flt-anthropic-0167.lean`

- `(hcomm : q'.comp p' = q''.comp p'')` (variable): Apply hpb to (0, 0), whose compatibility follows from RingHom.map_zero without hcomm. By RingHom.map_sub and h', h'', both b₁ - b₂ and 0 project to (0, 0). Uniqueness therefore gives b₁ - b₂ = 0, and sub_eq_zero gives b₁ = b₂. This argument also covers trivial rings.

### [`P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.KcSemiLocalIwasawaHaar.coe_nGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.lean#L1038-L1038) — `flt-anthropic-0168`

Snippet: `samples/flt-anthropic/flt-anthropic-0168.lean`

- `[NumberField L]` (variable): This instance is automatically included but unnecessary. The definition nGL is AutomorphicForm.unipotentGL2, whose matrix value is definitionally !![1, x; 0, 1] over any commutative ring. The tensor-product ring structure requires no NumberField L instance. Thus omitting [NumberField L] leaves the statement well-formed and the proof remains rfl, for every x, including zero.

### [`P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData.V_eq_O`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.lean#L489-L504) — `flt-anthropic-0182`

Snippet: `samples/flt-anthropic/flt-anthropic-0182.lean`

- `[LocallyOfFiniteType f]` (variable): This follows from D. Each c k is a closed immersion, hence locally of finite type; awayι₀ is an open immersion, and ProjSpace.π is proper, hence locally of finite type. Composition and D.hover give LocallyOfFiniteType ((D.U k).ι ≫ f). Apply IsZariskiLocalAtSource.of_iSup_eq_top with D.hcov. Install the recovered instance and use the original proof. This argument also handles an empty cover and trivial rings.
- `[QuasiCompact f]` (variable): Each D.U k is affine: D.c k is a closed immersion into an affine scheme, so use isAffine_of_isAffineHom. Thus each U k is compact. The finite cover D.hcov and isCompact_iUnion imply CompactSpace X. Since Spec A is quasi-separated, quasiCompact_of_compactSpace recovers QuasiCompact f, after which the original proof applies. Finite-union compactness includes the empty-cover case, and no nontriviality of A is required.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.AlgebraicCurve.AlgebraicCurve.adeleBddPrincipal_eq_comap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean#L791-L793) — `flt-anthropic-0183`

Snippet: `samples/flt-anthropic/flt-anthropic-0183.lean`

- `[HasPrincipalDivisors K F]` (theorem): The definitions of adeleBddPrincipal, adeleBdd, globalSub and adeleSpace do not require this instance. Put S = adeleBdd D, T = globalSub K F and C = adeleSpace K F. The required comap identity holds whenever S ≤ C, supplied unconditionally by adeleBdd_le_adeleSpace: if x ∈ C decomposes as s + t with s ∈ S and t ∈ T, then s ∈ C and t = x - s ∈ C, giving the required decomposition inside C. The reverse inclusion follows by addition. Thus globalSub ≤ adeleSpace is unnecessary. This argument also covers empty Place types and zero submodules.

### [`P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE.ell_sub_eq_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.lean#L175-L187) — `flt-anthropic-0184`

Snippet: `samples/flt-anthropic/flt-anthropic-0184.lean`

- `(hf0 : f ≠ 0)` (theorem): Split on f = 0. In the nonzero case, use the existing proof. When f = 0, Place.ord_zero and hP give P v = 0 for every place. Since Divisor K F is Place K F →₀ ℤ, Finsupp.ext yields P = 0, and the conclusion follows by simplifying E - 0. This also works when the type of places is empty.

### [`P2MW.S_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel.GramAsm.pair_mem_degZero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_exists_depth_comp_depthCompLaw_depthValueLaw_sndDegLaw_surjective_repOfKer_repOfInvariant_principalGood_of_widthPinChar_of_isModel.lean#L238-L244) — `flt-anthropic-0191`

Snippet: `samples/flt-anthropic/flt-anthropic-0191.lean`

- `[Fact q.Prime]` (variable): Every level M, including zero, has places of degree one. For M ≠ 0, use deg_eq_one_modularFunctionFieldBar. By the definitions of divisorExpansions, modularFunctionFieldFull and laurentBaseChange, level zero is the compositum of all positive levels. Each positive level is finite over the field generated by j, by B2Deg.finiteDimensional_adjoin_jBar in S_ModularCurve_deg_eq_one_modularFunctionFieldBar. Thus level zero is algebraic over that field (IntermediateField.isAlgebraic_iSup), and B2Deg.deg_eq_one_of_isAlgebraic_adjoin gives degree one there too. This covers q = 0; the displayed degree calculation then proves the conclusion without primality.
- `[NeZero N]` (variable): The statement elaborates without this instance. For N ≠ 0 the original proof applies. For N = 0, the level is zero: its field is the compositum of the positive-level fields, hence algebraic over the field generated by j, using B2Deg.finiteDimensional_adjoin_jBar and IntermediateField.isAlgebraic_iSup. B2Deg.deg_eq_one_of_isAlgebraic_adjoin therefore makes both place degrees one, and the original degree subtraction is zero. Coincident places cause no exception, and an empty place type is vacuous. Both reported hypotheses can also be removed together.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.eq_span_tInvChart_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L2727-L2734) — `flt-anthropic-0199`

Snippet: `samples/flt-anthropic/flt-anthropic-0199.lean`

- `(ht : Transcendental κ t)` (variable): By aevalChart_surjective, hchartInv makes φ := aevalChart κ t⁻¹ surjective without transcendence. The proper ideal Ideal.comap φ.toRingHom 𝔮 contains X by h. Since span {X} is maximal (isMaximal_span_X_sub_C κ 0), Ideal.IsMaximal.eq_of_le identifies this comap with span {X}. Applying Ideal.map_comap_of_surjective and Ideal.map_span gives the desired equality. This argument also covers algebraic t and t = 0, where t⁻¹ = 0.

### [`P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.HeckeGammaH.sum_slash_beta_eq_heckeU_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean#L381-L463) — `flt-anthropic-0201`

Snippet: `samples/flt-anthropic/flt-anthropic-0201.lean`

- `(B : BezoutData M ℓ)` (theorem): B occurs nowhere else in the statement and can be reconstructed. By the definitions of gamma0Units and Gamma0Map, hρ identifies the value of the unit gamma0Units M ρ with ℓ. Thus ZMod.isUnit_iff_coprime gives Nat.Coprime ℓ M. Converting with Nat.isCoprime_iff_coprime supplies integers u, v satisfying u * ℓ + v * M = 1, hence a local BezoutData M ℓ. The original proof then applies unchanged. This also covers M = 1, where ZMod M is trivial.
- `[NeZero M]` (variable): The statement elaborates without this instance: beta and GammaH do not require it, and the quotient's finite-index instance requires only NeZero ℓ, supplied by primality. Moreover, B.huv implies M ≠ 0: if M = 0, then B.u * ℓ = 1 over ℤ, forcing the natural number ℓ to equal 1, contradicting its primality. Install the resulting local NeZero M instance and retain the original proof. Thus the newly admitted zero case is inconsistent with the remaining hypotheses.

### [`P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.RoadA.coe_τ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.lean#L325-L326) — `flt-anthropic-0219`

Snippet: `samples/flt-anthropic/flt-anthropic-0219.lean`

- `[NeZero M]` (variable): Neither modularFunctionFieldBar M nor τ M σ requires M ≠ 0: modularFunctionFieldFull is defined for every natural level, and arithmeticRingAut acts by coeffMap on the underlying Laurent series. With `omit [NeZero M] in`, the unchanged theorem still has proof `rfl`. This also holds at M = 0, since the equality is definitional independently of the level.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.R4TateModelKHb.Xc_def`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.lean#L362-L362) — `flt-anthropic-0230`

Snippet: `samples/flt-anthropic/flt-anthropic-0230.lean`

- `[CharZero L]` (variable): The definition of Xc uses only the field structure, not CharZero, so `omit [CharZero L] in` leaves the statement well-formed and the same `rfl` proof works. This includes positive characteristic: even when 12 = 0, its inverse is defined and both sides remain definitionally equal.

### [`P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc.Bdd.mul_small`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PowerSeries_dvd_of_forall_taylorShift_order_le.lean#L132-L135) — `flt-anthropic-0231`

Snippet: `samples/flt-anthropic/flt-anthropic-0231.lean`

- `(hρ0 : 0 ≤ ρ)` (theorem): For ρ ≥ 0, use the existing proof. Otherwise split on m = 0. When m = 0, small_zero_iff reduces the result to Bdd.mul, which requires no restriction on ρ. When m > 0, hQ (m - 1) gives 0 ≤ C' * ρ. Since ρ < 0 and hC' gives C' ≥ 0, necessarily C' = 0. Then hQ bounds every coefficient norm by zero, so norm_le_zero_iff and PowerSeries.ext give Q = 0. The conclusion follows because both its coefficient norms and its bound are zero.
- `(hC : 0 ≤ C)` (theorem): By the definition of Bdd, hP 0 gives ‖coeff 0 P‖ ≤ C. Thus norm_nonneg implies 0 ≤ C, recovering the deleted hypothesis for the existing proof, including when P = 0.
- `(hC' : 0 ≤ C')` (theorem): By the definition of Small, hQ m gives ‖coeff m Q‖ ≤ C' * ρ^(m-m) = C'. Combining this with norm_nonneg recovers 0 ≤ C' for the existing proof. This also works for m = 0 and ρ = 0, since the exponent is zero.

### [`P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.EtaleCoordK1a.rankAtStalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean#L13-L24) — `flt-anthropic-0236`

Snippet: `samples/flt-anthropic/flt-anthropic-0236.lean`

- `[Module.FinitePresentation S M]` (theorem): Unfold Module.rankAtStalk and localize directly at p, avoiding local constancy. Since S is a domain, p.asIdeal.primeCompl ≤ nonZeroDivisors S: every element outside p is nonzero. IsLocalization.rank_eq followed by IsLocalizedModule.rank_eq identifies the localized rank with Module.rank S M. Then hrank and Module.finrank_eq_of_rank_eq prove the conclusion. These lemmas require neither finite presentation nor flatness, so both hypotheses can be removed together. The argument also covers n = 0 and the zero module.
- `[Module.Flat S M]` (theorem): The same direct localization argument works without flatness: Module.rankAtStalk is the finrank of the localized module, not its residue-field fiber dimension. IsLocalization.rank_eq and IsLocalizedModule.rank_eq preserve rank when the denominators are non-zero-divisors, as they are here. Apply hrank and Module.finrank_eq_of_rank_eq. This includes torsion modules and rank zero, and also permits removing finite presentation simultaneously.

### [`P2MW.S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.SupersingularTop3.mem_of_ord_nonneg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.lean#L40-L46) — `flt-anthropic-0240`

Snippet: `samples/flt-anthropic/flt-anthropic-0240.lean`

- `(hf : f ≠ 0)` (theorem): Split on whether f = 0. In the zero case, the conclusion follows from w.toValuationSubring.zero_mem (and Place.ord_zero confirms the order hypothesis holds). In the nonzero case, use the original proof with the nonzero fact supplied by the case split.

### [`P2MW.S_RubinSilverberg_exists_polynomial_rsFamily.M4cP2.D52.PhiA_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_RubinSilverberg_exists_polynomial_rsFamily.lean#L410-L414) — `flt-anthropic-0247`

Snippet: `samples/flt-anthropic/flt-anthropic-0247.lean`

- `(hj : j < 21)` (theorem): The identity holds for every natural j. Retain the existing proof as a local bounded identity for i < 21. Form Q ∈ (ℤ[X])[X] by taking sidePlusA minus sideMinusA, lifting their first five polynomial arguments through Polynomial.C and replacing the final argument by the outer X. Its degree is at most 20: lhsPairAG has degree at most 20 in its final argument, and both Horner lists have length 21. Evaluation at each of the 21 distinct natural constants gives PhiPlusA i − PhiMinusA i = 0 by the bounded identity. Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero, applied over the integral domain ℤ[X], therefore gives Q = 0. Evaluating at the arbitrary constant j proves the conclusion without hj. This includes j = 0 and every j ≥ 21; no division or nonvanishing assumptions are involved.

### [`P2MW.S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.lean#L16-L30) — `flt-anthropic-0249`

Snippet: `samples/flt-anthropic/flt-anthropic-0249.lean`

- `[W.IsElliptic]` (theorem): The existing proof works unchanged without this instance. Affine.Point consists of nonsingular points and has its group structure over any field with decidable equality, including singular curves. IsTwoKernel imposes only degree, coefficient and divisibility conditions; eval_Psi2Sq_of_two_nsmul_eq_zero requires nonsingularity of the chosen point, not ellipticity. The zero-point case remains excluded by hQ.

### [`P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.R4RRN.FF_slash_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.lean#L366-L368) — `flt-anthropic-0250`

Snippet: `samples/flt-anthropic/flt-anthropic-0250.lean`

- `[NeZero M']` (variable): FF and its defining Gamma_le_conj do not require this instance. Omit it and prove the identity directly: definitionally, ⇑(FF hqM' f) = ⇑f ∣[k] (Dr q)⁻¹; substitute conjElem_eq, then use SlashAction.slash_mul and group cancellation. This avoids slash_conjElem_eq_FF, which also automatically includes the unnecessary instance. The argument works for M' = 0 as well (when coprimality forces q = 1); no division by M' occurs.

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.QMHecke12.exists_generator`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.lean#L368-L422) — `flt-anthropic-0252`

Snippet: `samples/flt-anthropic/flt-anthropic-0252.lean`

- `(hι : Function.Injective ι)` (variable): Remove hι from the include command; the existing proof works unchanged. It never uses hι: injectivity of qmPeriodMap is obtained from IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span, whose statement requires no injectivity assumption on ι. Its nonzero-parameter hypotheses follow from ne_zero_of_hB hB. Thus the proof already covers every ι allowed by the remaining assumptions, without an additional degenerate case.

### [`P2MW.S_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction.P2MMultE.β_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction.lean#L1110-L1113) — `flt-anthropic-0258`

Snippet: `samples/flt-anthropic/flt-anthropic-0258.lean`

- `[IsNoetherianRing O]` (variable): Mathlib's instance PrincipalIdealRing.isNoetherianRing derives this from [IsPrincipalIdealRing O]. Thus `omit [IsNoetherianRing O] in` removes the separate assumption while allowing the unchanged statement and proof to elaborate. The instance proves every ideal finitely generated from principality, with no additional nontriviality or exceptional-case assumptions.

### [`P2MW.S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.AlgebraicCurve.AlgebraicCurve.Place.stichtenothGenusExists_of_isFractionRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean#L2159-L2166) — `flt-anthropic-0261`

Snippet: `samples/flt-anthropic/flt-anthropic-0261.lean`

- `[HasPrincipalDivisors K F]` (variable): IsCurveOver extends HasPrincipalDivisors. After omitting this variable, obtain the instance from IsCurveOver.toHasPrincipalDivisors and use the existing proof. Neither the statement nor this implication requires additional nonemptiness assumptions.
- `[IsDomain A]` (theorem): IsFractionRing.isDomain_iff_isField implies IsDomain A because E is a field. Install this instance locally and retain the existing proof. IsFractionRing is defined without requiring IsDomain A; its injective algebra map into E also excludes the trivial-ring case.
- `[Nonempty (Place K F)]` (theorem): First obtain a PoleDivisorPackage P using hasPoleDivisorPackage_of_isFractionRing, which does not require this hypothesis. Its fields give degree P.B = P.n and 0 < P.n. If Place K F were empty, every divisor would be zero, so P.B would have degree zero, a contradiction. Install the resulting Nonempty instance and apply stichtenothGenusExists_of_hasPoleDivisorPackage as before.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.WeierstrassCurve.WeierstrassCurve.ModularCurve.kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean#L3405-L3408) — `flt-anthropic-0263`

Snippet: `samples/flt-anthropic/flt-anthropic-0263.lean`

- `[W.IsElliptic]` (variable): The existing proof works unchanged. The source of transcendental_polyToFunctionField_X (lines 2370–2375) requires only a field and an affine curve, using polyToFunctionField_injective. Thus singular curves are covered too; ellipticity is not required by the remaining binders.
- `[CharZero F]` (variable): The existing proof works unchanged: Transcendental.of_tower_top requires field structures and the F–F' algebra tower, not characteristic zero. Neither the remaining binders nor the polynomial-coordinate transcendence argument requires this hypothesis.
- `[CharZero F']` (variable): The existing proof works unchanged. Both transcendental_polyToFunctionField_X and Transcendental.of_tower_top are characteristic-independent. Polynomial-coordinate injectivity holds over every field, including positive characteristic.
- `[IsScalarTower R₀ F F']` (variable): The proof only restricts transcendence from F' to F. The required tower is F → F' → (W⁄F').FunctionField, supplied by the natural polynomial, quotient and fraction-ring structures. Compatibility with R₀ is unused, and no remaining binder requires it.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]` (variable): The existing proof works unchanged and uses no centred-place properties. The definition of AbelTheorem depends on GenusOnePlaceGate, not IsCentred, so the remaining binders still elaborate.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]` (variable): The existing proof works unchanged. Neither polynomial-coordinate injectivity nor restriction of transcendence uses AbelTheorem, and no remaining binder depends on this instance.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]` (variable): The existing proof works unchanged: transcendental_polyToFunctionField_X uses only polynomial-coordinate injectivity, not places or centredness. AbelTheorem does not depend on IsCentred.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]` (variable): The existing proof works unchanged. The transcendence lemma requires only a field and an affine curve, and Transcendental.of_tower_top uses no Abel-theorem assumption. No remaining binder depends on this instance.

### [`P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.lean#L229-L413) — `flt-anthropic-0266`

Snippet: `samples/flt-anthropic/flt-anthropic-0266.lean`

- `[Finite G]` (theorem): In CQAux.range_ι_comp_eq_univ, finiteness is used only to prove W closed. This is unnecessary: hπW identifies π.base '' W with π.base '' U, which is closed by hUcl and π.isClosedMap. Replace h1 with this argument and remove hWclosed and the Fintype instance. Everything else works for arbitrary groups. Propagate this generalization through exists_mem_translate, iSup_preimage_inf_eq and le_iSup_preimage_imagePreimage; the solution proof then works unchanged. The nonempty image needed for connectedness still follows from hUconn.nonempty.
- `(hsurj : Function.Surjective π.base)` (theorem): This follows from [IsFinite π] and hsec. The range of π.base is closed by Scheme.Hom.isClosedMap. Let V be its open complement; then π ⁻¹ᵁ V = ⊥. Sections over ⊥ are subsingleton (Scheme.lean), so hsec V forces Γ(X,V) to be subsingleton. If V were nonempty, Scheme.component_nontrivial would contradict this. Thus V is empty and π.base is surjective. This also handles empty schemes. Derive hsurj locally and retain the original proof.

### [`P2MW.S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.lean#L203-L596) — `flt-anthropic-0267`

Snippet: `samples/flt-anthropic/flt-anthropic-0267.lean`

- `(hS : ∀ q ∈ S, q.Prime)` (theorem): Used only to make the avoidance modulus in hEis positive. Replace that modulus by level N r qv * ∏ q ∈ S.erase 0, q. Finset.prod_ne_zero_iff and Finset.mem_erase give positivity. Any prime ℓ belonging to S belongs to S.erase 0, so Finset.dvd_prod_of_mem still proves the chosen prime lies outside S. This handles zero and composite entries of S, including an empty product; the remaining proof is unchanged.
- `(hSmin : Smin ⊆ S)` (theorem): The proof only needs inclusion for prime members of Smin. Recover this restricted inclusion using hNS: when q = p use hpN, and otherwise use hNmin. Also obtain p ∈ S directly from hNS p Fact.out hpN. Replace the uses of hSmin by these facts; every remaining application concerns a prime. Nonprime or zero entries of Smin therefore cause no problem.
- `(htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)` (theorem): Neither the remaining statement nor the proof uses htame. The displayed proof works unchanged after deleting it, including when Smin has no members distinct from p.
- `(hrN : ¬ r ∣ N * p)` (theorem): Recover ¬ r ∣ N from hrS and hNS r hr. Obtain p ∈ S from hNS p Fact.out hpN, hence r ≠ p from hrS. Nat.prime_dvd_prime_iff_eq then gives ¬ r ∣ p, and Nat.Prime.not_dvd_mul gives hrN. Insert this derivation before the existing proof. Primality excludes zero-prime degeneracies.

### [`P2MW.S_Function_orbitCensus_of_dihedralThree_relations.P2MKcOrbitCensus.b_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean#L14-L17) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- `[Fintype X]` (variable): The existing proof works unchanged without finiteness: applying b twice to b x = b y and rewriting with hb gives x = y. This works for arbitrary X, including empty types. Both instance hypotheses can be deleted together.
- `[DecidableEq X]` (variable): Neither Function.Injective nor the proof requires decidable equality. The existing congrArg argument and rewriting by hb work unchanged for arbitrary X, including empty types. Both instance hypotheses can be deleted together.

### [`P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.KcHaarQuotientMulRight.lintegral_density_mul_comp_mul_right_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.lean#L75-L109) — `flt-anthropic-0270`

Snippet: `samples/flt-anthropic/flt-anthropic-0270.lean`

- `[LocallyCompactSpace G]` (theorem): Split on whether G is locally compact. In the positive case, use the existing proof. Otherwise, G cannot be weakly locally compact: IsTopologicalGroup.regularSpace supplies RegularSpace, hence R1Space, and WeaklyLocallyCompactSpace.locallyCompactSpace would give a contradiction. Thus the condition in HaarQuotient.weight is false, so weight and density are identically zero. Both integrals are zero, including when f takes ∞, since ENNReal.zero_div and zero multiplication apply.
- `[SFinite μH]` (theorem): Recover this instance from the remaining assumptions. Install LocallyCompactSpace H using hH.locallyCompactSpace; H inherits second countability, hence is sigma-compact. IsHaarMeasure extends IsFiniteMeasureOnCompacts, so SigmaFinite.of_isFiniteMeasureOnCompacts gives SigmaFinite μH, and the SigmaFinite-to-SFinite instance supplies SFinite μH. The original proof then works unchanged. This also covers trivial groups.

### [`P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.UqNSol.fstDiv_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean#L358-L366) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- `[hqN : Fact (¬ q ∣ N)]` (variable): Neither PlaceSpecialization nor fstDiv requires this instance. After omitting hqN, unfold PlaceSpecialization.fstDiv and apply Finsupp.filter_sum s f under classical. This proves the unchanged statement even when q divides N, including for an empty sum.

### [`P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.LCMazur.OrdQ.span_singleton_eq_range_ordProj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.lean#L263-L272) — `flt-anthropic-0275`

Snippet: `samples/flt-anthropic/flt-anthropic-0275.lean`

- `(h2 : finrank A V = 2)` (theorem): This follows from hφ. IsLocalRing supplies Nontrivial A, and LinearMap.charpoly_natDegree identifies the characteristic polynomial's natural degree with finrank A V. Polynomial.Monic.natDegree_mul and Polynomial.natDegree_X_sub_C show that the right-hand side of hφ has natural degree 2. Derive h2 this way and use the existing proof.
- `[IsLocalRing A]` (variable): A direct coordinate argument avoids locality. If A is trivial, Module.subsingleton makes V trivial, so the conclusion holds. Otherwise choose a basis b indexed by Fin 2 using h2, and put ψ = φ - β • 1. The characteristic-polynomial identity gives trace φ = α + β, hence trace ψ = α - β, using charpoly_eq_of_finrank_eq_two and eq_of_quadratic_eq. By hw choose c₀,c₁ with ψ(b i) = cᵢ • w. Writing w = x₀ • b 0 + x₁ • b 1, the matrix trace formula gives c₀*x₀ + c₁*x₁ = α - β. Consequently ψ(w) = (α - β) • w, so ordProj_apply and hu give ordProj φ α β w = w. Thus A ∙ w is contained in the range; the reverse inclusion is exactly the existing argument using hw. This also covers w = 0 without cancellation.

### [`P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.lean#L27-L40) — `flt-anthropic-0278`

Snippet: `samples/flt-anthropic/flt-anthropic-0278.lean`

- `(ha : a ≠ 0)` (theorem): Split on whether a = 0. In the nonzero case, use the existing proof. If a = 0, AbsoluteValue.map_zero gives μ a = 0, hence μ a < 1; the subtype element ⟨a, haA⟩ equals zero in A, which belongs to maximalIdeal A by Ideal.zero_mem. Thus both sides hold in the excluded case.

### [`P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.TH1Wanted2.inv_mem_and_const_mem_of_gaussPresentation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.lean#L874-L964) — `flt-anthropic-0285`

Snippet: `samples/flt-anthropic/flt-anthropic-0285.lean`

- `(hq3 : q = 3)` (theorem): Neither the remaining statement nor the proof uses hq3. The same proof works for every prime q; the retained primality instance supplies the nonzero condition required by qExpand.
- `(hqM' : ¬ q ∣ M')` (theorem): Unused in the remaining statement and proof. The Laurent-series witnesses work unchanged when q divides M'; the separate nonzero assumptions remain.
- `(hK₁ : FiniteDimensional ↥k₀ ↥K₁)` (theorem): Unused in the remaining statement and proof. The constant-membership argument uses only hA₁, halg and hO, and works for infinite-dimensional K₁ as well.
- `(IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤)` (theorem): Introduced as hK1 and never used. Delete its introduction and retain the rest of the proof unchanged. No generation property of F₀ is needed, including when this supremum is proper.
- `(∀ (K' : IntermediateField ↥k₀ (AlgebraicClosure ℚ)), FiniteDimensional ↥k₀ ↥K' → ∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑K' : Set (AlgebraicClosure ℚ))) ⊔ F₀) → LinearIndependent ↥K' c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0)` (theorem): Introduced as hLD and never used. Removing this premise and its introduction leaves the proof unchanged; no linear-disjointness argument or restriction on these families is needed.
- `(∀ f : ↥(fieldBar q M'), (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ Set.range ⇑(coeffEmb (AlgebraicClosure ℚ)) → f ∈ F₀)` (theorem): Introduced as hRAT and never used. Removing it and its introduction leaves the proof unchanged. Membership of these rational-coefficient series in F₀ plays no role.
- `[Fact (j₁ ≠ 0)]` (theorem): Remove instj₁ and hjt0, and prove hjq0 directly. By the definition of coeffEmb, jqModC_rat and map_jqModC, coeffEmb (AlgebraicClosure ℚ) jq equals jqModC (AlgebraicClosure ℚ). Its coefficient at −1 is 1 by ModularCurve.coeff_jqModC_neg_one, so it is nonzero. The rest of the proof is unchanged. Thus hj₁ already excludes j₁ = 0, without this instance.

### [`P2MW.S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.P2mConormLSpace.CFE.trace_algebraMap'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.lean#L193-L203) — `flt-anthropic-0287`

Snippet: `samples/flt-anthropic/flt-anthropic-0287.lean`

- `[FiniteDimensional K K']` (variable): Retain separability and split on finite dimensionality. The finite case uses the original proof. Otherwise F'/F is also infinite-dimensional: every finite subextension E/K of K'/K has a primitive element θ by Field.powerBasisOfFiniteOfSeparable; the preceding minpoly_algebraMap_eq_map, specialized to E, preserves its minimal-polynomial degree over F. Thus [E:K] is bounded by [F':F] if the latter is finite. But an infinite algebraic extension has finite subextensions of arbitrarily large degree (adjoin arbitrarily large finite linearly independent sets, using IntermediateField.finiteDimensional_adjoin). Consequently both traces vanish by Algebra.trace_eq_zero_of_not_exists_basis. This handles every k, including zero. This deletion retains separability; the two reported deletions cannot generally be combined.
- `[Algebra.IsSeparable K K']` (variable): Retain finite dimensionality and split on separability. The separable case uses the original proof. In the nonseparable case F'/F cannot be separable: otherwise every algebraMap K' F' x would be separable over F, and minpoly_algebraMap_eq_map hconst together with Polynomial.separable_map would imply every x is separable over K. Algebra.trace_eq_zero_of_not_isSeparable therefore makes both traces zero, including at k = 0. No finite-dimensionality assumption on F'/F is needed for that lemma. This deletion retains finite dimensionality; the two reported deletions cannot generally be combined.

### [`P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.lean#L110-L138) — `flt-anthropic-0294`

Snippet: `samples/flt-anthropic/flt-anthropic-0294.lean`

- `[IsDomain A]` (theorem): The remaining assumptions imply this instance: `IsFractionRing.injective A K` gives an injective ring homomorphism from A into the field K, and `Function.Injective.isDomain` pulls back its domain structure. Insert `letI : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)` before the existing proof. Neither IsFractionRing nor IsIntegrallyClosed requires IsDomain to elaborate. Injectivity into the nontrivial field also excludes the trivial-ring case.

### [`P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.WNormSwapSol.θ_θ_γel`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.lean#L941-L962) — `flt-anthropic-0295`

Snippet: `samples/flt-anthropic/flt-anthropic-0295.lean`

- `(hpM2 : ¬ p ^ 2 ∣ M)` (variable): This follows from hd. The image of d is a unit, so hd makes (p : ZMod (M / p)) a unit. By ZMod.isUnit_prime_iff_not_dvd, p ∤ M / p. Nat.dvd_div_iff_mul_dvd hpM then gives ¬ p² ∣ M. Derive hpM2 this way and retain the original proof. These lemmas also handle modulus 1 or 0.
- `(hζ : IsPrimitiveRoot ζ p)` (variable): Neither ζ nor hζ occurs in the conclusion or the remaining hypotheses. Since Qb is algebraically closed of characteristic zero and p is prime, HasEnoughRootsOfUnity.exists_isPrimitiveRoot supplies a primitive pth root in Qb. Convert it to a unit using IsPrimitiveRoot.isUnit and IsPrimitiveRoot.isUnit_unit, then run the original proof with this chosen root instead. Primality ensures p ≠ 0, so there is no exceptional zero-order case; the chosen unit is nonzero as required by the coefficient argument.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.AlgebraicCurve.DiscRigidity.sum_filter_eq_of_degreeOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.lean#L80-L105) — `flt-anthropic-0299`

Snippet: `samples/flt-anthropic/flt-anthropic-0299.lean`

- `(hf : f ≠ 0)` (theorem): Split on f = 0. In the zero case, hDf and AlgebraicCurve.Place.ord_zero (Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:125) give Df v = 0 for every v, so both finite sums are zero, including when the indexing types or sets are empty. In the nonzero case, the existing proof applies unchanged.


## Formal Frontier (18 flagged)

### [`GradedRing.Veronese.adjoin_component_one_eq_top`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseDegreeOne.lean#L80-L104) — `formal-frontier-0005`

Snippet: `samples/formal-frontier/formal-frontier-0005.lean`

- `(hn : 0 < n)` (theorem): Split into n = 0 and 0 < n; the positive case uses the existing proof. For n = 0, VeroneseZero.lean defines zeroVariable 𝒮, the degree-one copy of 1, which belongs to component 𝒮 0 1 by mem_component_iff. Its lemma of_zero_eq_algebraMap_mul_pow expresses every direct-sum generator as a degree-zero coefficient times a power of zeroVariable. Thus Algebra.subset_adjoin and closure under coefficients, multiplication, powers and addition prove the conclusion by DirectSum.induction_on. This zero-index argument needs neither hgen nor nontriviality and works for the zero ring too.

### [`Nat.DivisionGrowth.affine_lower_bound`](https://github.com/FormalFrontier/sequence-growth/blob/7b7db3df8a043a09d037de4ff1eced6873404fb2/SequenceGrowth/Data/Nat/DivisionGrowth.lean#L68-L94) — `formal-frontier-0117`

Snippet: `samples/formal-frontier/formal-frontier-0117.lean`

- `(hs : 0 < s)` (theorem): Split on s = 0. When s ≠ 0, recover hs using Nat.pos_of_ne_zero and retain the existing proof. When s = 0, Nat.zero_sub_one, div_zero and zero_div make both ratio and offset zero. The conclusion is equality for m = 0 and reduces to 0 ≤ (u m : ℚ) for positive m, proved by positivity. Thus the zero-denominator case also holds.

### [`AlgebraicGeometry.reducedIdentityComponent_topologicalKrullDim`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/Dimension.lean#L265-L296) — `formal-frontier-0126`

Snippet: `samples/formal-frontier/formal-frontier-0126.lean`

- `[IsAlgClosed K]` (variable): Let H be the reduction and C its identity component. The existing setup gives H a group structure and a locally finite-type structure morphism without algebraic closure. The earlier theorem ringKrullDim_stalk_unit_eq_topologicalKrullDim identifies H's dimension with its unit-stalk dimension over any field. The unit lies in C by Scheme.mem_identityComponent_iff. Since C → H is an open immersion, coheight_eq_of_isOpenImmersion and ringKrullDim_stalk_eq_coheight identify the corresponding stalk dimensions. Order.coheight_le_krullDim then gives dim H ≤ dim C; the reverse inequality follows from the inclusion's inducing map, exactly as in the existing identity-component proof. Finish with Scheme.reduction_topologicalKrullDim. These bounds require no finite-dimensionality assumption. Empty cases cannot occur because the field spectrum is nonempty and the unit supplies a point; zero-dimensional cases also satisfy the same argument.

### [`SpectralStoneDuality.chosenLimitCylinder_subset_iff_eventually`](https://github.com/FormalFrontier/spectral-stone-duality/blob/78b803577679fc37120fa3406833af653fe12018/SpectralStoneDuality/LimitCylinderDescent.lean#L251-L261) — `formal-frontier-0141`

Snippet: `samples/formal-frontier/formal-frontier-0141.lean`

- `[HasLimit F]` (theorem): Mathlib's TopCat.topCat_hasLimitsOfShape supplies limits because J : Type v is small in universe max v u. Thus HasLimit F is inferred automatically after deleting this binder, and the existing proof works unchanged. This includes empty stages and empty limits; the limit construction requires no nonemptiness.

### [`CategoryTheory.CartesianMonoidalCategory.tensorLeftIsoProd_hom_app_fst`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/SingleCoverGroup.lean#L58-L63) — `formal-frontier-0146`

Snippet: `samples/formal-frontier/formal-frontier-0146.lean`

- `[HasBinaryProducts K]` (variable): CartesianMonoidalCategory already supplies a HasFiniteProducts instance (Cartesian/Basic.lean), and hasLimitsOfShape_discrete supplies HasBinaryProducts. Omitting this variable therefore leaves the statement elaboratable and the original proof unchanged. HasBinaryProducts is a proposition, so proof irrelevance ensures the inferred instance does not change the statement's chosen products. The construction requires no additional nonemptiness or nontriviality assumptions.

### [`IsKrasner.adjoin_rootSet_le_adjoin_rootSet_of_norm_coeff_sub_lt`](https://github.com/FormalFrontier/polynomial-root-stability/blob/ceae7822f6151ec6626678db1653054d3398cff3/PolynomialRootStability/Krasner.lean#L363-L391) — `formal-frontier-0152`

Snippet: `samples/formal-frontier/formal-frontier-0152.lean`

- `(hε : 0 < ε)` (theorem): Already follows from hcoeff 0: 0 ≤ ‖g.coeff 0 - f.coeff 0‖ < ε. Recover hε with this inequality and use the existing proof; ε ≤ 0 is impossible.
- `(hfm : f.Monic)` (theorem): In the source of the root-continuity lemma, reference monicity is used only to show that a reference root forces positive degree. Instead, hfsep.ne_zero and Polynomial.natDegree_pos_of_aeval_root give positive degree. Reproduce the continuity estimate with this replacement, then retain the Krasner argument unchanged. Nonzero constants have no roots, so their case is vacuous; zero is excluded by separability.
- `(hdeg : g.natDegree = f.natDegree)` (theorem): Split on degree equality and use the existing proof when equal. Otherwise, Monic.coeff_natDegree and coeff_eq_zero_of_natDegree_lt show that the coefficient difference at the larger degree has norm 1, hence hcoeff gives 1 < ε. Real.one_le_rpow then shows the radius in hbound is at least ‖x‖. For each reference root x, hbound therefore supplies Krasner's condition with y = 0. Separability and minimal-polynomial splitting follow exactly as in the existing rootwise Krasner lemma. Thus x belongs to K₀⟮0⟯ = ⊥ by IntermediateField.adjoin_zero, proving the desired inclusion. Empty root sets, including degree zero, are vacuous.

### [`Subgroup.exists_continuous_coset_representative`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ContinuousCosetRepresentative.lean#L55-L74) — `formal-frontier-0160`

Snippet: `samples/formal-frontier/formal-frontier-0160.lean`

- `[T2Space G]` (variable): TotallyDisconnectedSpace.t1Space supplies T1Space G. Thus {1} is closed, and IsTopologicalGroup.t2Space_iff_one_closed supplies T2Space G. After omitting this hypothesis, install the derived T2Space instance and reuse the original proof unchanged. The conclusion's quotient topology does not require T2Space. This also works for trivial groups; Group already excludes empty types.

### [`MvPowerSeries.isUnit_adicallyRestricted_iff_coeff_radical`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean#L83-L92) — `formal-frontier-0162`

Snippet: `samples/formal-frontier/formal-frontier-0162.lean`

- `[IsAdicComplete I R]` (variable): Completeness is unnecessary. Forward, map a unit to the ambient power-series ring and through adicReduction I 1; MvPowerSeries.isUnit_iff_constantCoeff and MvPolynomial.isUnit_iff give the required conditions. Conversely, the unit constant coefficient gives an ambient formal inverse g by MvPowerSeries.isUnit_iff_constantCoeff. For each k > 0, Ideal.radical_pow and MvPolynomial.isUnit_iff show that adicReduction I k f is a polynomial unit. Its polynomial inverse equals the coefficientwise reduction of g, by uniqueness of inverses and adicReduction_coe. Thus isAdicallyRestricted_iff_map_mem_poly_range shows that g is restricted, proving IsUnit f. For k = 0 the quotient is the zero ring, so the polynomial-range condition is automatic. This argument also covers empty σ, the zero ring, and I = ⊥ or ⊤, without completeness or separatedness.

### [`FundamentalGroup.existsUnique_hom_of_isOpenCover`](https://github.com/FormalFrontier/fundamental-groupoids/blob/2fdb99858e3feb7a6a06ae10915f286364de2cc1/FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean#L404-L527) — `formal-frontier-0164`

Snippet: `samples/formal-frontier/formal-frontier-0164.lean`

- `(hU : IsPathConnected (U : Set X))` (theorem): Replace the global frame on U by a frame on its basepoint path component, choosing the prescribed intersection paths there, and send all arrows in other components to 1. No arrows connect different components, so this defines a functor. The intersection lies entirely in the basepoint component by hI; consequently compatibility is unchanged. FundamentalGroupoid.descOfIsOpenCover and inclusion_comp_descOfIsOpenCover then give existence. For uniqueness, subdivide any based loop into alternating U- and V-contained segments. Every switching point lies in the intersection; connecting these points to p inside the intersection expresses the loop as a product of images of based loops in U and V. Thus those images determine every homomorphism. The point p excludes empty charts and intersection; other components and trivial groups cause no exceptions. Both hU and hV can be deleted simultaneously.
- `(hV : IsPathConnected (V : Set X))` (theorem): Symmetrically, construct the V frame only on its basepoint path component and assign 1 to arrows in every other component. By hI all intersection points remain in the framed component, so the compatible functors descend using FundamentalGroupoid.descOfIsOpenCover. Uniqueness follows by subdividing based loops and connecting switching points to p within the intersection, showing that the two chart fundamental groups generate the ambient fundamental group. No connectedness of V is needed. Empty charts are excluded by p, and additional components or trivial groups do not affect the argument. Both hU and hV can be deleted simultaneously.

### [`GradedRing.Veronese.finiteType_of_finiteType`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseFiniteType.lean#L105-L126) — `formal-frontier-0179`

Snippet: `samples/formal-frontier/formal-frontier-0179.lean`

- `(hn : 0 < n)` (theorem): Split on n = 0. For positive n, use the existing proof. For n = 0, `GradedRing.Veronese.finiteType_zero` in `GradedRings/VeroneseZero.lean` proves exactly the required conclusion, without any finite-type or nontriviality assumption. Its proof generates the external zero-index direct sum by its degree-one copy of 1 over its degree-zero component. Importing that file therefore allows hn to be deleted, including for trivial rings.

### [`AlgebraicGeometry.Proj.degreeScaledChartMap_preimage_basicOpen`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/DegreeScaledMap.lean#L453-L469) — `formal-frontier-0188`

Snippet: `samples/formal-frontier/formal-frontier-0188.lean`

- `(hn : 0 < n)` (theorem): The degree-zero case also holds. Write a = (i.2 : A). Every chart point maps into basicOpen 𝒜 a, and its inclusion lies in basicOpen ℬ (f a). Apply the existing positive-degree proof to r * a, homogeneous of positive degree when n = 0. Then basicOpen_mul and map_mul cancel these chart factors, giving the desired equality for r. This argument also handles zero elements and empty charts.
- `(hr : r ∈ 𝒜 n)` (theorem): The equality holds for arbitrary r. DegreeScaledMapPoint.lean proves degreeScaledMap_mem_pointIdeal for every ring element. Restrict it along (chartCover 𝒜 ℬ f).f i, use chartCover_map and the chart inclusion identity, and apply mem_basicOpen. To avoid circular dependence, retain the given positive-homogeneous proof as an internal helper and reproduce that file's degree-zero and homogeneous-decomposition arguments. These work pointwise, including zero and empty charts. Both hr and hn can be removed together.

### [`finiteGroupPresentation_iff_compact_totallyDisconnected`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/FiniteGroupCharacterization.lean#L198-L214) — `formal-frontier-0200`

Snippet: `samples/formal-frontier/formal-frontier-0200.lean`

- `[T2Space G]` (theorem): The proof works unchanged without this binder. The forward direction only transfers compactness and total disconnectedness along P.equiv. In the reverse direction, ProfiniteGrp.of requires Group, TopologicalSpace, IsTopologicalGroup, CompactSpace, and TotallyDisconnectedSpace, but not T2Space. Total disconnectedness supplies T1Space via TotallyDisconnectedSpace.t1Space, and a T1 topological group is Hausdorff. This includes the trivial group; Group G excludes the empty case.

### [`SheafCohomology.CompactOpenSections.explicitSectionsComparison_surjective`](https://github.com/FormalFrontier/sheaf-cohomology/blob/93674a2a8f1ad19b2c87b20c3f5e0898b7e38f43/SheafCohomology/CompactOpenSections.lean#L534-L740) — `formal-frontier-0225`

Snippet: `samples/formal-frontier/formal-frontier-0225.lean`

- `[HasLimitsOfSize.{u, u} C]` (variable): Global existence of limits is unnecessary. CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf shows that every sheaf used here remains a sheaf after composing with forget C, using only the retained limit-preservation assumption. TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types then provides elementwise gluing and uniqueness. Use these to replace the concrete-category gluing/local-equality lemmas, also in the proof of the injectivity helper. The remaining filtered-colimit argument is unchanged. Empty covers are included in this gluing result, so empty U causes no exception. This hypothesis and the reflection hypothesis can even be removed together.
- `[instReflectsIsomorphisms : (forget C).ReflectsIsomorphisms]` (variable): Only the forward transfer of the sheaf condition to underlying types is needed. CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf requires limit preservation, not reflection of isomorphisms. Apply TopCat.Presheaf.IsSheaf.isSheafUniqueGluing_types to obtain gluing and local equality, replacing the corresponding concrete-category lemmas both here and in the injectivity helper. All other steps remain valid without reflection. The type-valued gluing theorem handles empty covers as well. This hypothesis and global limit existence can be removed together.

### [`AlgebraicGeometry.Scheme.Hom.ker_radical_of_isReduced_source`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L154-L160) — `formal-frontier-0232`

Snippet: `samples/formal-frontier/formal-frontier-0232.lean`

- `[QuasiCompact f]` (theorem): By definition, f.ker is the largest ideal sheaf contained componentwise in the section-map kernels. Since X is reduced, each such kernel is radical by Ideal.isRadical_bot.comap. Thus f.ideal_ker_le and Ideal.IsRadical.radical_le_iff show that f.ker.radical remains componentwise contained in those kernels. IdealSheafData.le_ofIdeals_iff then gives f.ker.radical ≤ f.ker; the reverse inequality is IdealSheafData.le_radical. This replaces ker_apply without requiring quasi-compactness and also covers empty schemes and trivial section rings.

### [`AlgebraicGeometry.iInf_ker_eq_vanishingIdeal_iSup_closure_range`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L176-L185) — `formal-frontier-0233`

Snippet: `samples/formal-frontier/formal-frontier-0233.lean`

- `[∀ j, QuasiCompact (f j)]` (theorem): For any morphism g from a reduced scheme, g.ker equals the vanishing ideal I of its range closure without quasi-compactness. The inequality g.ker ≤ I follows from Hom.range_subset_ker_support, closedness of support, and IdealSheafData.le_support_iff_le_vanishingIdeal. Conversely, a section in I.ideal U vanishes on the range, so its pullback has empty basic open (Scheme.preimage_basicOpen). Reducedness makes this pullback zero by eq_zero_of_basicOpen_eq_bot. Thus IdealSheafData.le_ofIdeals_iff and the definition of Hom.ker give I ≤ g.ker. Apply this equality pointwise and retain the existing vanishingIdeal_iSup argument. Empty sources cause no exception; for an empty indexing type both sides are ⊤ by vanishingIdeal_bot.

### [`Module.Basis.exists_basis_subset_finset_of_le_jacobson`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/LinearAlgebra/Basis/Semilocal.lean#L383-L393) — `formal-frontier-0252`

Snippet: `samples/formal-frontier/formal-frontier-0252.lean`

- `(hJ : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤ (Ideal.jacobson (⊥ : Ideal B)))` (theorem): Replace the auxiliary unit-selection argument by finite avoidance over R. Using IsLocalRing.residue_surjective, choose representatives t(a) of the infinite residue field. For distinct a,b, t(a)-t(b) is a unit by IsLocalRing.residue_ne_zero_iff_isUnit. Consequently, finitely many nonzero R-linear maps on W are simultaneously nonzero: inductively, take y avoiding the previous kernels and x outside the next kernel, then choose y+t(a)•x. Each map excludes at most one parameter unless it vanishes on x, in which case a previously avoided map excludes none. Two excluded parameters would contradict IsUnit.smul_eq_zero. Apply this to the restrictions of P.asIdeal.mkQ.comp f for all maximal ideals P. As in the existing proof, hW and surjectivity of f ensure each restriction is nonzero. The selected f-value avoids every maximal ideal, hence is a unit by exists_max_ideal_of_mem_nonunits. The existing basis-update induction then applies without hJ. Empty families cause no problem: if B is the zero ring, every value is a unit; if s is empty, retain b.

### [`ContinuousCohomology.coind₁_positive_eq_zero`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/CoinducedAcyclic.lean#L374-L413) — `formal-frontier-0278`

Snippet: `samples/formal-frontier/formal-frontier-0278.lean`

- `[DiscreteTopology X]` (theorem): Compactness and the topological-group structure make G locally compact. For arbitrary topological coefficients Y, construct swap as f ↦ curry ((uncurry f).comp swap) and diagonal evaluation as f ↦ (uncurry f).comp (t ↦ (t,t)). Their continuity follows from ContinuousMap.continuous_curry, ContinuousMap.continuous_uncurry, and ContinuousMap.continuous_precomp, found in Mathlib/Topology/CompactOpen.lean; discreteness is unnecessary. These maps have exactly the original pointwise formulas and equivariance proofs. Recreate the recursive insertion with them, omitting the discrete-topology instances. The pointwise alternating-sum proof of its contracting identity remains unchanged, as does the theorem’s subsequent homology argument. This works for arbitrary X, including the zero representation, and for the trivial group.

### [`MvPowerSeries.existsUnique_firstVariable_division_of_scalar_top`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableDivision.lean#L112-L132) — `formal-frontier-0285`

Snippet: `samples/formal-frontier/formal-frontier-0285.lean`

- `(hprim : Ideal.span (Set.range (fun index : Fin (n + 1) →₀ ℕ => coeff index (f : MvPowerSeries (Fin (n + 1)) V))) = ⊤)` (theorem): Derive hprim from htop and hc. By MvPolynomial.finSuccEquiv_coeff_coeff and coeff_restrictedResidue, the coefficient of f at (0 : Fin n →₀ ℕ).cons d reduces to c ≠ 0. It therefore lies outside the maximal ideal and is a unit. Its coefficient ideal is consequently ⊤, using Ideal.eq_top_of_isUnit_mem. This exact argument appears in FirstVariablePreparation.lean, lines 119–139. Then use the existing proof. It works for d = 0 and n = 0. This hypothesis and hc can each be deleted individually, but not generally both.
- `(hc : c ≠ 0)` (theorem): The retained hprim implies restrictedResidue a ham f ≠ 0: otherwise coeff_restrictedResidue puts every coefficient of f in the proper maximal ideal, contradicting hprim. Its image under finSuccEquiv is therefore nonzero. Polynomial.leadingCoeff_ne_zero and Polynomial.coeff_natDegree, together with hdegree and htop, give MvPolynomial.C c ≠ 0, hence c ≠ 0. Recover hc and use the existing proof. This includes d = 0 and n = 0. This hypothesis and hprim cannot generally both be deleted.
- `(ha : a ≠ 0)` (theorem): Split on a = 0; the nonzero branch uses the existing proof. When a = 0, hrad forces the maximal ideal to be ⊥, since the zero ideal of a domain is radical. The definition of IsAdicallyRestricted at level 1 then says that every restricted series has finite support, so these rings are polynomial rings. Reduction modulo the maximal ideal is injective, so hdegree, htop and hc say that f, viewed as a polynomial in the first variable, has degree d and a nonzero scalar leading coefficient. That scalar is a unit because the maximal ideal is zero. Normalize f to monic and use Polynomial.modByMonic_add_div, Polynomial.degree_modByMonic_lt and Polynomial.div_modByMonic_unique, transporting back through polynomialRestrictedFinFirst. This also handles d = 0 (zero remainder), n = 0 and zero dividends; IsDomain excludes the trivial coefficient ring.

