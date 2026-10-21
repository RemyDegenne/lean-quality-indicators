# unnecessary-hypotheses: run `main`, judge `gpt-6-luna-high`

| Library | Sampled | Judged | Flagged | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|
| Mathlib | 1000 | 300 | 12 | 4.0% | 2.3%–6.9% | unknown |
| Tau Ceti | 1000 | 300 | 19 | 6.3% | 4.1%–9.7% | unknown |
| Lean Pool | 1000 | 300 | 48 | 16.0% | 12.3%–20.6% | unknown |
| FLT (Anthropic) | 1000 | 300 | 61 | 20.3% | 16.2%–25.2% | unknown |
| Formal Frontier | 1000 | 300 | 15 | 5.0% | 3.1%–8.1% | unknown |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (12 flagged)

### [`Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L275-L280) — `mathlib-0027`

Snippet: `samples/mathlib/mathlib-0027.lean`

- `[NormedAddCommGroup E]` (variable): `InnerProductSpace 𝕜 E` already supplies the `SeminormedAddCommGroup E` structure needed for the statement and proof. The projection and inner-product lemmas used here require that seminormed structure, not the stronger `NormedAddCommGroup`; removing this variable leaves the theorem statement elaborated and the same proof works.

### [`RatFunc.Luroth.Φ_natDegree_eq_φ_natDegree`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/RatFunc/Luroth.lean#L182-L185) — `mathlib-0077`

Snippet: `samples/mathlib/mathlib-0077.lean`

- `(h : E ≠ ⊥)` (theorem): When E = ⊥, X is transcendental over E, so minpoly E X—and hence φ E—is zero. Its mapped polynomial is zero; integerNormalization_eq_zero_iff gives Φ' E = 0, and primPart_zero gives Φ E = 1. Thus both natDegrees are 0 (natDegree_zero and natDegree_one), so the equality still holds. The proof can split on E = ⊥ and use this case; the existing proof handles the other case.

### [`MeasureTheory.projectiveFamilyContent_mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean#L134-L137) — `mathlib-0116`

Snippet: `samples/mathlib/mathlib-0116.lean`

- `(hs : s ∈ measurableCylinders α)` (theorem): If `hs` is false, `projectiveFamilyContent_eq` and the definition of `projectiveFamilyFun` give `projectiveFamilyContent hP s = 0`, so the result follows from nonnegativity of `ℝ≥0∞`. If `hs` is true, the existing `addContent_mono` proof applies. The other hypotheses remain necessary for that argument: `ht` ensures the larger set is in the content's domain, and `hst` supplies monotonicity.

### [`WeierstrassCurve.preΨ_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean#L314-L318) — `mathlib-0123`

Snippet: `samples/mathlib/mathlib-0123.lean`

- `[Nontrivial R]` (theorem): The assumption follows from the theorem’s hypothesis `h`: `nontrivial_of_ne (n : R) 0 h` yields `Nontrivial R`. Install that as a local instance and the existing proof using `W.preΨ'_ne_zero` applies unchanged. This also handles the trivial-ring case: there, `h` cannot hold, so the implication is vacuous.

### [`AdicCompletion.tensor_map_id_left_injective_of_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean#L367-L373) — `mathlib-0139`

Snippet: `samples/mathlib/mathlib-0139.lean`

- `[Module.Finite R M]` (variable): This can be deleted on its own: flatness of `AdicCompletion I R` over the Noetherian ring `R` makes tensoring on the left preserve injective linear maps for arbitrary `M` and `N`. A proof can establish flatness via `Module.Flat.iff_lTensor_injective'` (as in `flat_of_isNoetherian` immediately below, reducing to finite ideals), then apply flatness to `f`. The conclusion and its tensor products require no finiteness assumption.
- `[Module.Finite R N]` (variable): This can be deleted on its own: flatness of `AdicCompletion I R` over the Noetherian ring `R` makes tensoring on the left preserve injective linear maps for arbitrary `M` and `N`. A proof can establish flatness via `Module.Flat.iff_lTensor_injective'` (as in `flat_of_isNoetherian` immediately below, reducing to finite ideals), then apply flatness to `f`. The conclusion and its tensor products require no finiteness assumption.

### [`Convex.norm_image_sub_le_of_norm_fderiv_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/MeanValue.lean#L498-L504) — `mathlib-0148`

Snippet: `samples/mathlib/mathlib-0148.lean`

- `[NontriviallyNormedField 𝕜]` (variable): This assumption follows from `[IsRCLikeNormedField 𝕜]`: use `IsRCLikeNormedField.rclike 𝕜` and `RCLike.norm_ofReal` at `2` to exhibit an element of norm greater than `1`, yielding a `NontriviallyNormedField` instance. The theorem can retain its statement unchanged and locally install that instance before applying the existing mean-value argument. This also covers the scalar field’s normed structure; no degenerate case is excluded.

### [`Submodule.norm_sq_eq_add_norm_sq_starProjection`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L607-L610) — `mathlib-0170`

Snippet: `samples/mathlib/mathlib-0170.lean`

- `[NormedAddCommGroup E]` (variable): This supplies more structure than the theorem needs. `InnerProductSpace 𝕜 E` already carries a `SeminormedAddCommGroup E` instance, which suffices for the norm notation and the Pythagorean identity; the identity and the projection argument do not require norm separation. Thus the result remains true with the same statement after dropping this variable, including in degenerate seminormed inner product spaces. The existing proof proceeds via `norm_sq_eq_add_norm_sq_projection` and `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`, neither of which requires `NormedAddCommGroup E`.

### [`Set.sub_mem_Ico_iff_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Interval/Set/Group.lean#L98-L99) — `mathlib-0180`

Snippet: `samples/mathlib/mathlib-0180.lean`

- `[PartialOrder α]` (variable): The equivalence only needs a preorder: the two conjuncts are rearranged using the order-translation facts `sub_lt_comm` and `le_sub_comm`, which do not use antisymmetry. `IsOrderedAddMonoid α` already has a `[Preorder α]` parameter, so the statement's intervals and inequalities remain available without `[PartialOrder α]`; the proof is unchanged.

### [`continuous_parametric_integral_of_continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/Bochner/Set.lean#L1121-L1139) — `mathlib-0190`

Snippet: `samples/mathlib/mathlib-0190.lean`

- `[FirstCountableTopology X]` (theorem): This is needed by the proof’s use of `continuousAt_of_dominated`, but not by the result. Around any `x₀`, continuity of `‖f‖` and compactness of `s` give a neighborhood `V` of `x₀` and a finite bound for `‖f x y‖` on `V × s`: use product neighborhoods at each `(x₀,y)`, take a finite subcover of `s`, and intersect the corresponding neighborhoods of `x₀`. Apply `continuousOn_of_dominated` on `V` with that constant bound, which is integrable on the restricted measure because `hs.measure_ne_top`; this gives continuity at `x₀` without first countability.
- `[LocallyCompactSpace X]` (theorem): The proof uses this to choose a compact neighborhood, but compactness of a neighborhood in `X` is unnecessary. The same finite-cover argument from compactness of `s` and continuity of `‖f‖` gives a neighborhood `V` of each `x₀` on which the integrand is uniformly bounded over `s`. Then `continuousOn_of_dominated` on `V` gives continuity at `x₀`, with the constant bound integrable since `hs.measure_ne_top`. This argument works without local compactness.

### [`MeasureTheory.VectorMeasure.ennrealVariation_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/VectorMeasure/Variation/Basic.lean#L60-L62) — `mathlib-0192`

Snippet: `samples/mathlib/mathlib-0192.lean`

- `(hs : MeasurableSet s)` (theorem): The equality also holds when `s` is not measurable: `toENNRealVectorMeasure_apply` gives `μ.ennrealVariation s = 0` in that case, and a vector measure's value on a nonmeasurable set is zero, so `μ.variation s = 0` as well. Thus the measurability argument can be deleted; the measurable case is exactly `toENNRealVectorMeasure_apply_measurable`.

### [`add_tsub_add_le_tsub_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Sub/Defs.lean#L160-L162) — `mathlib-0260`

Snippet: `samples/mathlib/mathlib-0260.lean`

- `[AddLeftMono α]` (variable): This monotonicity follows from `OrderedSub` and commutativity, so the instance can be constructed without assuming it. For `u ≤ v` and `c`, `tsub_le_iff_right` gives `(c + u) - c ≤ u` (using `add_comm`); hence `(c + u) - c ≤ v`, and another application gives `c + u ≤ v + c = c + v`. This supplies `AddLeftMono α`, after which the theorem's proof goes through. The argument also covers degenerate cases since it uses only the stated `OrderedSub` equivalence and commutativity.

### [`MeasureTheory.Measure.prod_smul_left`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Prod.lean#L877-L881) — `mathlib-0275`

Snippet: `samples/mathlib/mathlib-0275.lean`

- `[hν : SFinite ν]` (variable): The product is defined for arbitrary measures: `Measure.prod` uses the junk value `0` when its second measure is not s-finite. Without this instance, split on whether `SFinite ν` holds. In the true case, use the existing proof with that instance; in the false case both products are `0`, so the equality follows from `c • 0 = 0`. This covers arbitrary `μ` and `c`, including zero measures.


## Tau Ceti (19 flagged)

### [`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/Basic.lean#L952-L963) — `tauceti-0001`

Snippet: `samples/tauceti/tauceti-0001.lean`

- `(hN : N ≠ 0)` (theorem): At the excluded case N = 0, `Nat.primeFactors 0` is empty, so both products are 1 and the right-hand side is 0. By `Gamma0_mem` and the file's `mem_Gamma0_iff_dvd`, `Gamma0 0` consists of matrices with lower-left entry 0. The matrices with rows `(1, 0)` and `(n, 1)` for n ∈ ℕ represent pairwise distinct cosets: the quotient of two such matrices has lower-left entry the difference of their parameters, and belongs to `Gamma0 0` only when that difference is 0. Thus the quotient is infinite and its `Nat.card`—hence the subgroup index, defined as `Nat.card` of the quotient in Mathlib's `GroupTheory/Index.lean`—is 0. The left-hand side is therefore also 0. For N ≠ 0 the displayed proof applies unchanged using hN, with the zero case handled separately.

### [`TauCeti.AffineDynkinType.not_module_finite_preprojectiveAlgebra`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Quiver/Preprojective/InfiniteDimensional.lean#L279-L288) — `tauceti-0002`

Snippet: `samples/tauceti/tauceti-0002.lean`

- `[Fintype V]` (variable): The theorem’s graph vertices are `Fin t.nodes`, which are finite without this supplied `Fintype` instance. The local `Fintype.ofFinite` instance can provide the `Fintype` structures needed for the preprojective algebra from the corresponding `Finite` instances; the source comments at lines 76–78 describe this setup. Thus the conclusion remains provable after omitting `[Fintype V]`.

### [`TauCeti.ContCohomology.homogeneous2_coe_apply_one`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/Shapiro/Basic.lean#L460-L466) — `tauceti-0005`

Snippet: `samples/tauceti/tauceti-0005.lean`

- `[IsTopologicalGroup G]` (variable): This instance can be deleted while leaving the statement well-typed. `DiscreteCoind` is defined using only `[Group G]` and `[TopologicalSpace G]` (with the subgroup and coefficient action), and `homogeneous2` uses only the group and action structure. The displayed `simp` proof uses the defining formula and coinduced-function equivariance, neither of which requires a topological-group law. Thus the theorem remains true for any topology on `G`, including degenerate cases.

### [`HeckeRing.GLn.posDetInt_le_commensurator`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/HeckeRing/GLn/Basic.lean#L712-L717) — `tauceti-0020`

Snippet: `samples/tauceti/tauceti-0020.lean`

- `[NeZero n]` (variable): The statement’s definitions (`posDetInt`, `SLnZ`, and the commensurator) do not require `NeZero n`. The cited `mem_commensurator_of_hasIntEntries` proof uses it, but the case `n = 0` can be handled separately: `Fin 0` is empty, so `GL (Fin 0) ℚ` is trivial and the claimed inclusion holds. For `n ≠ 0`, retain the existing proof using that lemma. Thus the instance can be omitted while keeping the statement unchanged.

### [`ContRepresentation.isUnitary_iff_norm_map`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Continuous/Unitary/Basic.lean#L51-L58) — `tauceti-0058`

Snippet: `samples/tauceti/tauceti-0058.lean`

- `[NormedAddCommGroup V]` (variable): `InnerProductSpace 𝕜 V` supplies the `SeminormedAddCommGroup V` structure needed for the representation, norms, and `LinearMap.norm_map_iff_inner_map_map`. That lemma is stated with seminormed, not normed, additive groups, so the proof works without this stronger instance. The conclusion and `IsUnitary` remain well-typed, including for zero or trivial spaces.

### [`TauCeti.Multiquadratic.exists_mem_sq_eq_intCast`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/Multiquadratic/Cyclotomic/Embedding.lean#L122-L139) — `tauceti-0071`

Snippet: `samples/tauceti/tauceti-0071.lean`

- `(hN : 0 < N)` (theorem): `hζ : IsPrimitiveRoot ζ N` already forces `N ≠ 0`: if `N = 0`, then `ζ ^ 1 = 1` would imply `0 ∣ 1` by `hζ.dvd_of_pow_eq_one`, a contradiction. Hence `N > 0` follows. Without `hN`, derive this positivity from `hζ` and use it wherever the proof currently passes `hN` (including `exists_mem_sq_eq_natCast` and `hζ.pow`). This also rules out the degenerate case `N = 0`; no extra assumption on `m` is needed.

### [`TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Data/Nat/Factorization/GcdSplit.lean#L56-L71) — `tauceti-0078`

Snippet: `samples/tauceti/tauceti-0078.lean`

- `(hp : p.Prime)` (theorem): The statement does not otherwise use `hp`. Without it, split on whether `p` is prime: in the prime case the existing proof applies; otherwise Mathlib's `Nat.ordCompl_of_not_prime` gives `ordCompl[p] m = m` and `ordCompl[p] n = n`, while `Nat.factorization_eq_zero_of_not_prime` makes both exponents zero. Thus the right side reduces to `Nat.gcd m n * p ^ 0 = Nat.gcd m n`, including `p = 0`. The nonzero assumptions on `m` and `n` remain in place.

### [`TauCeti.integrable_norm_sub_sq_of_hasFiniteMoment`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Basic.lean#L929-L938) — `tauceti-0099`

Snippet: `samples/tauceti/tauceti-0099.lean`

- `[SecondCountableTopology E]` (variable): The conclusion and its measurability arguments do not require second countability. Without this instance, one can derive the needed L² bounds directly: use `HasFiniteMoment.memLp` with `measurable_edist_right.aestronglyMeasurable` to get `MemLp` of the distance from zero, then `memLp_map_measure_iff` to transfer that bound along each projection, and finally apply `memLp_two_iff_integrable_sq_norm` to the difference. These measurability facts follow from `[OpensMeasurableSpace E]`; the argument works as well for trivial or empty types. The finite-measure assumption remains relevant, since infinite mass at two distinct points can have finite marginal moments while the squared displacement is not integrable.

### [`TauCeti.exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Cohomology.lean#L195-L206) — `tauceti-0118`

Snippet: `samples/tauceti/tauceti-0118.lean`

- `[CharZero L]` (variable): This follows from the retained `[Algebra ℚ_[p] L]` and the characteristic-zero instance on `ℚ_[p]`, via `Algebra.charZero_of_charZero`. Removing the binder therefore leaves the needed instance available for the proof; the field and algebra assumptions also rule out a degenerate exception.
- `[CharZero K]` (variable): This follows from the retained `[Algebra ℚ_[p] K]` and the characteristic-zero instance on `ℚ_[p]`, via `Algebra.charZero_of_charZero`. Removing the binder therefore leaves the needed instance available for the proof; the field and algebra assumptions also rule out a degenerate exception.

### [`Matrix.ProjectiveSpecialLinearGroup.isParabolic_inv_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup/FinTwo.lean#L103-L117) — `tauceti-0134`

Snippet: `samples/tauceti/tauceti-0134.lean`

- `[NoZeroDivisors R]` (variable): The statement and `IsParabolic` definition do not require this assumption; it is used by `isParabolic_mk_iff` only to classify quotient representatives. Instead, use the existential definition directly: a parabolic SL representative of `g` has an inverse representative of `g⁻¹`, and conversely. In the 2×2 calculations, inversion preserves the discriminant and preserves the condition of being non-scalar: the adjugate has the same diagonal-equality and off-diagonal-zero conditions. These facts hold over any commutative ring, including the zero ring and rings with zero divisors, so the equivalence remains true without `[NoZeroDivisors R]`.

### [`TauCeti.Manifold.christoffelMap_coordChange`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/Coordinate/Change.lean#L52-L207) — `tauceti-0155`

Snippet: `samples/tauceti/tauceti-0155.lean`

- `[CompleteSpace 𝕜]` (variable): The coordinate-change identity does not depend on completeness of the scalar field. The transformation argument uses differentiability of coordinate changes and algebraic frame-coefficient formulas, which apply over a nontrivially normed field without assuming it complete. The proof can be adapted by establishing the flat frame derivative’s additivity and Leibniz rules directly from the derivative rules used in `isCovariantDerivativeOn_frameCovariantDerivative` in `LocalFrame.lean`; those rules do not require completeness. No excluded zero or empty case is involved.

### [`TauCeti.integralBockstein_modulus_one`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/Bockstein/Integral.lean#L265-L271) — `tauceti-0157`

Snippet: `samples/tauceti/tauceti-0157.lean`

- `[CompactSpace G]` (variable): For modulus 1, the range criterion gives `1 • y = 0` for every value `y` of the Bockstein, hence `y = 0`. The criterion follows from exactness of the coefficient sequence and does not require compactness; compactness is used for vanishing of integral degree-one cohomology elsewhere, not for this zero-map result. Thus the Bockstein is zero without `[CompactSpace G]`, including degenerate cases.

### [`TauCeti.ContCohomology.indexTwoShortExact_explicitDelta0`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/Coinduced/IndexTwo.lean#L177-L186) — `tauceti-0185`

Snippet: `samples/tauceti/tauceti-0185.lean`

- `[CompactSpace G]` (variable): Compactness is not used in the statement or the proof. The connecting-map formula follows from `DiscreteShortExact.explicitDelta0_apply` using the chosen preimage and the cocycle identity; these constructions require the stated group, topology, action, and exact-sequence assumptions, but not compactness. The `H0` and `H1` definitions likewise impose no compactness assumption, so the theorem remains well-formed and provable without `[CompactSpace G]`.

### [`TauCeti.exists_coprimePart_indK0_of_trivial_eq_nsmul`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Permutation/PrimePower.lean#L131-L148) — `tauceti-0194`

Snippet: `samples/tauceti/tauceti-0194.lean`

- `[Fact p.Prime]` (variable): This instance can be deleted. From `[CharP k p]`, `CharP.char_is_prime_or_zero k p` splits into `p.Prime` or `p = 0`. In the prime case, locally install `Fact p.Prime` and use the existing proof. In the zero case, take `D = C`: since `G` is finite, `Nat.card C` is positive, so `¬ 0 ∣ Nat.card C`; also `D.relIndex C = 1` and `0 ^ (Nat.card C).factorization 0 = 1`, making the class equality reflexive. Thus the conclusion holds in both cases without the argument.

### [`TauCeti.cwEulerChar_preimage_of_card_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/Covering.lean#L75-L88) — `tauceti-0231`

Snippet: `samples/tauceti/tauceti-0231.lean`

- `(hfin : ∀ b, Finite ↥(p ⁻¹' {b}))` (variable): The uniform finite-fiber assumption can be removed. For each cell center, `hd` gives its fiber cardinality `d`. If `d > 0`, `Nat.finite_of_card_ne_zero` makes each such fiber finite, enough to count the lifted cells via `cellPreimageEquiv` and the finite set of base cells. If `d = 0`, a fiber may be empty or infinite, but either has `Nat.card = 0`; the same cell decomposition then gives zero cardinality for every lifted cell, so the lifted Euler characteristic and the right-hand side are both zero. The existing `nat_card_cell_preimage` lemma does not require `hfin`; in the positive case its cell-count argument can use the finiteness of the fibers over centers supplied by `hd`.

### [`TauCeti.EisensteinSeries.weightedEisensteinSeries_charWeight_slash`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/ModularForms/EisensteinSeries/Character.lean#L166-L177) — `tauceti-0236`

Snippet: `samples/tauceti/tauceti-0236.lean`

- `[NeZero N]` (theorem): It cannot be deleted: at N = 0, Mathlib defines `ZMod.val` as `Int.natAbs` (Mathlib `Data/ZMod/Basic.lean`, lines 51–59), so `charWeight` loses the sign of its arguments. For example, take u = 3, v = 1, an odd character ψ modulo 3, trivial φ, and γ = -I ∈ Gamma0 0. The weight is even under x ↦ -x, whereas the slash action by -I contributes (-1)^k; for even k the left side is the original series but the claimed scalar is ψ(-1)φ(-1) = -1. Thus the transformation law need not hold at N = 0.

### [`TauCeti.schwarzChristoffelEdgeAngle_comp_strictMono`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/GlobalTurning.lean#L114-L125) — `tauceti-0238`

Snippet: `samples/tauceti/tauceti-0238.lean`

- `[LocallyFiniteOrder ι]` (variable): The conclusion and the definition of `schwarzChristoffelEdgeAngle` require only the finite type and linear order; local finiteness is needed by the proof’s interval-sum lemma, not by the result. Without this instance, unfold the angle into its sum over `Finset.univ`, express the difference using a finite filter, and use `StrictMono a` to identify that filter with the indices between the two arguments. The sum is negative because it contains the later index and every exponent is negative, giving the strict increase. This argument also covers empty or singleton domains, where strict monotonicity is vacuous.

### [`WeierstrassCurve.mem_integralPoints_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/Integral.lean#L71-L76) — `tauceti-0255`

Snippet: `samples/tauceti/tauceti-0255.lean`

- `[(W.baseChange ℚ).IsElliptic]` (variable): The ellipticity instance is not needed: `integralPoints` is defined directly as the set of points satisfying the displayed existential, and `mem_integralPoints_iff` is `Iff.rfl`. The source also proves the helper lemmas for base change without this instance (`omit [(W.baseChange ℚ).IsElliptic]`). The statement’s point and equation types are meaningful for a non-elliptic curve as well, so dropping the instance leaves the statement unchanged and valid, including in degenerate cases.

### [`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isCompact`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/PDE/Regularity/HolderContinuity.lean#L238-L258) — `tauceti-0281`

Snippet: `samples/tauceti/tauceti-0281.lean`

- `[Nonempty ι]` (theorem): If `ι` is nonempty, the existing proof via the compact-set drift theorem applies. If `ι` is empty, `EuclideanSpace ℝ ι` is a subsingleton, so every `K` is subsingleton and `Set.Subsingleton.holderOnWith` gives the conclusion for any function, with exponent `1` and constant `0`. Thus the existence statement also holds in the zero-dimensional case.


## Lean Pool (48 flagged)

### [`ViscositySolns.exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Aleksandrov/JetCalculus/Strictification/StrictifiedObjective.lean#L337-L370) — `lean-pool-0000`

Snippet: `samples/lean-pool/lean-pool-0000.lean`

- `(hr : 0 <= r)` (theorem): If `hr` is removed and `r < 0`, `Metric.closedBall` is empty: membership means `dist x 0 ≤ r`, contradicting `dist_nonneg`. The definition of `CoordinateSemiconvexOn` quantifies over points in the set, so on this empty ball it holds vacuously (for example with `lambda = 0`). This also covers the zero-dimensional case, since the distance is still nonnegative. When `r ≥ 0`, the existing proof applies. Thus the proof can split on `le_total 0 r`, using the existing argument in the nonnegative case and vacuity in the negative case.

### [`AVenhance.Infra.Section4.iterate_corrected_material_unnormalized`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section4/IteratesMaterialBudgetAmplitude.lean#L20-L43) — `lean-pool-0006`

Snippet: `samples/lean-pool/lean-pool-0006.lean`

- `(hi : 2 ≤ i)` (theorem): The cases i = 0 and i = 1 also satisfy the conclusion, so the proof can split on those cases and use the existing remainder bound for i ≥ 2. By the definitions of iterateAmplitude, the amplitudes at indices 0 and 1 are 1 and C₀ * q, respectively. For i = 0 the inequality reduces, after using C ≥ 0, to 2q² + q ≤ 2/C₀² + 1/C₀; for i = 1 it reduces to q² + q + 1/C₀² ≤ 1/C₀ + 2/C₀². Both follow from 0 < q, 0 < C₀ and C₀ * q ≤ 1. For i ≥ 2 the existing proof applies unchanged.

### [`NavierStokes.ParticularWaveBounds.pressure_class`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ParticularWaveBounds.lean#L1371-L1389) — `lean-pool-0009`

Snippet: `samples/lean-pool/lean-pool-0009.lean`

- `(hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)` (theorem): A uniform upper bound on N is not needed for the conclusion. The lower bound and hb give ‖N n x‖ ≥ b > 0, so the inverse-square factor is smooth on the domain. Its derivatives are finite sums of products of derivatives of N divided by powers of ‖N‖²; the lower bound controls those denominators, while hN supplies polynomial-growth bounds for the numerator factors. Thus the inverse-square factor, and hence the pressure coefficient and final band-scaled expression, retain the required class bounds without hupper. This also covers the zero case: the lower bound excludes N = 0 wherever the domain is nonempty, and an empty domain makes the pointwise bounds vacuous.

### [`Bananas.marks_ne_of_allSubmodular_banana`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BrillNoetherGraphs/Bananas/Theta/ThetaBoundarySubmodularity.lean#L847-L855) — `lean-pool-0015`

Snippet: `samples/lean-pool/lean-pool-0015.lean`

- `(hg : 1 ≤ g)` (theorem): Without `hg`, genus zero is allowed, and the conclusion can fail: take a genus-zero banana (one strand of length one) and set `u = v`. Its graph is connected and genus zero, so `rank_eq_degree_or_neg_one_of_connected_genus_zero` gives the rank profile `-1` for negative-degree divisors and degree otherwise. For a repeated mark, `rankDelta` is the second difference of this profile after subtracting two chips; it is nonnegative for every divisor (it is 1 in degree 0 and 0 in every other degree). Thus `hSub` holds although `u = v`. The positive-genus assumption is needed for the proof's negative-rank-delta witness, but not for the theorem after that assumption is deleted.

### [`IsoGraph.Canon.splitCell_tr_general`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Equivariance.lean#L3331-L3342) — `lean-pool-0028`

Snippet: `samples/lean-pool/lean-pool-0028.lean`

- `(hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))` (theorem): The conclusion concerns only `.tr`. In the general branch, the trace is determined by `boundsFrom`; the scatter result only feeds later state fields and does not affect that trace. The proof can unfold the split and project its trace, using `hbd` for the `boundsFrom` result, without identifying the scatter output via `hsc`.
- `(hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))` (theorem): The conclusion concerns only `.tr`. The write result affects `lab` and `pos`, not the trace, which is determined by the subsequent `boundsFrom` computation. Projecting the trace of the split therefore does not require this equality; `hbd` supplies the trace result.

### [`ESS.buCut_gradient_absorption`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUShortGradient.lean#L28-L102) — `lean-pool-0033`

Snippet: `samples/lean-pool/lean-pool-0033.lean`

- `(hκ : 0 ≤ buCutScalar κ z)` (theorem): Split on the sign of `buCutScalar κ z`. If it is nonnegative, the proof's square-root scaling step applies as written. If it is negative, the left side is nonpositive because `Real.sqrt` is nonnegative, while the right side is nonnegative from `hM`, `vec3EuclideanNorm_nonneg`, and `Real.sqrt_nonneg`. Thus the inequality holds without this hypothesis.
- `(hM : 0 ≤ M)` (theorem): This follows from `hderiv`: evaluate it at any `j : Fin 3` (for example `0`), and combine `abs_nonneg` with `|spatialPartial (buCutScalar κ) j z| ≤ M`. The rest of the proof can use this derived nonnegativity in place of `hM`.

### [`IsoGraph.Canon.individualize_refines`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Progress.lean#L192-L202) — `lean-pool-0038`

Snippet: `samples/lean-pool/lean-pool-0038.lean`

- `(hv : v < n)` (theorem): When `v ≥ n`, `p.pos[v]!` defaults to 0. If `n = 0`, `Refines` is vacuous. Otherwise, `hp` ensures position 0 belongs to the cell starting at 0, and `individualize` only changes `cst` entries within that first cell, where `hp.cellCst` shows the old values are 0. Thus no old cell start is lost. A proof can split on `v < n`: use the existing argument in that case, and unfold `individualize` and `setCstFrom` to establish preservation for the default-index case.

### [`TauCeti.DavisKahanExt.le_riccati_small_root_of_quadratic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Riccati/BoundedSharpEstimates.lean#L41-L89) — `lean-pool-0045`

Snippet: `samples/lean-pool/lean-pool-0045.lean`

- `(hd : 0 < d)` (theorem): It follows from the remaining hypotheses: `hb` gives `0 ≤ 2 * b`, and `hsmall` gives `2 * b < d`, hence `0 < d`. The proof can derive `hd` this way and proceed unchanged; this also covers `b = 0`.

### [`EulerOrdinarySobolev.Evolution.gradient_logarithmic_envelope`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/OrdinaryEulerBKM.lean#L109-L141) — `lean-pool-0078`

Snippet: `samples/lean-pool/lean-pool-0078.lean`

- `(hC : 0 ≤ C)` (variable): The other hypotheses imply `0 ≤ C`. Evaluate `hlog` at `⟨0, le_rfl, hT⟩`: its left side is nonnegative by `U.gradientNormPath_nonneg`. On the right, the factor `1 + ‖…‖ + W t * log (exp 1 + tensorNorm …)` is at least `1`, since norms and `tensorNorm` are nonnegative, `log (exp 1 + tensorNorm …) ≥ 1`, and `hW` holds. Thus `C` cannot be negative. Derive `hC` this way and the proof can proceed unchanged; the conclusion does not otherwise require this argument.

### [`NavierStokes.SignedCopyBounds.local_mul`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SignedCopyBounds.lean#L91-L97) — `lean-pool-0090`

Snippet: `samples/lean-pool/lean-pool-0090.lean`

- `(hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)` (theorem): This can be deleted while keeping `hv`. For each bound order, choose the constant `A ≥ 0` from `hf.bounds`. If `A > 0`, the order-zero bound at any `x ∈ K n i` forces `w n x ≥ 0`, since the other factors in `majorant` are positive. If `A = 0`, all derivatives of `f n i` through that order vanish there, so the product derivatives vanish and the output bound can use constant zero. Thus the bilinear estimate can proceed at each point of `K` without `hw`; outside `K` the conclusion imposes no bounds.
- `(hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x)` (theorem): Symmetrically, this can be deleted while keeping `hw`: if the constant from `hg.bounds` is positive, its order-zero bound forces `v n x ≥ 0` on `K n i`; if it is zero, all derivatives of `g n i` through the chosen order vanish there and the product bound uses constant zero. Hence the product estimate needs no `hv`.

### [`RS.kernelSubobject_tensorHom_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/KernelPow.lean#L729-L761) — `lean-pool-0091`

Snippet: `samples/lean-pool/lean-pool-0091.lean`

- `[MonoidalPreadditive A]` (theorem): This follows from the other assumptions: rigidity gives tensoring on either side adjoints, so those functors preserve finite biproducts; since `A` is abelian, they are additive. Their additivity supplies the whiskering zero/additivity laws required by `MonoidalPreadditive`. Thus that structure can be obtained without assuming it separately, and the kernel/image argument still applies.

### [`Egrs75.ClearingP3.lowDigits_half_pred_pow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Egrs75/SubtractBranch.lean#L172-L181) — `lean-pool-0093`

Snippet: `samples/lean-pool/lean-pool-0093.lean`

- `(hp : 3 ≤ p)` (theorem): The result also holds for the only odd base below 3, namely p = 1: then (1^m - 1) / 2 = 0 and LowDigits 1 0 holds because Nat.digits 1 0 = []. For p ≠ 1, Odd p implies 3 ≤ p, so the existing induction applies. Thus hp can be removed, handling p = 1 separately and deriving 3 ≤ p otherwise.

### [`NFChoice.Compiler.NFCompactLeafFinalGate.axSiCompact`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NFWeakPartition/NFCompactLeafFinalGate.lean#L209-L255) — `lean-pool-0096`

Snippet: `samples/lean-pool/lean-pool-0096.lean`

- `(hzw : z ≠ w)` (theorem): If `z = w`, the target's two nested universal binders update the same variable, so its body is the diagonal case where both terms have value `W`. The literal `axSi` hypothesis `hLit` still applies: choose its existential witness for `v x`, then use `hY W W` for each `W`. The remaining distinctness hypotheses preserve the values of `x` and `y`; both `z` and `w` map to `W`, so the pair-membership equivalence proves the target. Thus one can split on `z = w`, using the existing argument when they differ and this diagonal argument when they coincide.

### [`NavierStokes.TerminalCompensation.physicalProfile_family_contDiffOn`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalCompensation.lean#L1082-L1099) — `lean-pool-0105`

Snippet: `samples/lean-pool/lean-pool-0105.lean`

- `(hR : 0 < R)` (theorem): The conclusion holds for every real R. If R = 0, z.2 / R is constantly 0, so the base-profile factor is constant and the correction term is smooth by composition; the remaining factor is smooth from ha. If R ≠ 0, z.2 / R is nonzero throughout the domain. Real rpow is smooth on either the positive or negative half-line (on the negative half-line, use its exp/log-absolute-value and cosine formula), so the base-profile composition is smooth there. The correction term is smooth for any R by the existing composition argument, and the product/sum proof then goes through. Thus the positivity hypothesis is only used to invoke the positive-argument rpow lemma, not required by the statement.

### [`NavierStokes.PolarCharts.chart_finiteJets_uniform`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalGraphBounds.lean#L336-L354) — `lean-pool-0108`

Snippet: `samples/lean-pool/lean-pool-0108.lean`

- `(ha : 0 < a)` (theorem): The bound holds for every real `a`. For `a = 0`, `positiveRadius 0 x = 0` for every `x` (division by zero gives zero and `Real.smoothTransition.zero_of_nonpos` applies), so `chart 0 j` is constant. For `a < 0`, the radial `positiveRadius (a ^ 2 / 32)` remains smooth and positive; the angular denominator `positiveRadius (a / 8) x` is strictly negative: if `x > a / 8`, the transition argument is negative and the value is `a / 8`, while if `x ≤ a / 8`, the transition is nonnegative and the value is at most `a / 8`. Thus division by it and the subsequent `arctan` are smooth. Consequently `chart a j` is smooth also for `a < 0`; the existing compact-ball/continuous-iterated-derivative argument then proves the same bound without `ha`. The cases `a = 0` and `a < 0` avoid any singularity in the chart.

### [`NavierStokes.SlowStressSupport.axial_stress_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SlowStressSupport.lean#L2093-L2133) — `lean-pool-0111`

Snippet: `samples/lean-pool/lean-pool-0111.lean`

- `(hn : 0 < n)` (theorem): The statement does not otherwise require n > 0. In the proof, hn is used only to establish `n - 1 ≤ n`; that holds for every natural n by `Nat.sub_le _ _`, including n = 0. Replacing the definition of `hprev_le` with that lemma leaves the subsequent proof steps unchanged, and the other hypotheses provide the required data in the n = 0 case as well.

### [`NumberField.Odlyzko.summable_integral_norm_idealSet_complexPlaceMellinGaussian`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/CompletedZeta/ConeGaussianInterchange.lean#L96-L112) — `lean-pool-0115`

Snippet: `samples/lean-pool/lean-pool-0115.lean`

- `[IsTotallyComplex K]` (variable): The integral need not be evaluated using the totally-complex formula: integrating each place separately gives a constant times the product of the embedding factors |w(x)|^{-2 s.re}. On the fundamental cone, the normalized embedding coordinates are uniformly comparable, so this product is bounded by a constant times |Norm(x)|^{-α}, where α = 2 s.re (r₁+r₂)/[K:ℚ] ≥ s.re > 1. The resulting series is controlled by `summable_idealSet_inverseNormPower` at exponent α. This also covers fields with real places; ideal-set elements are nonzero, so no zero-value exception arises.

### [`CKN.Leray.mildShiftedStokesIntegral_continuous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierMildIntegral.lean#L216-L225) — `lean-pool-0117`

Snippet: `samples/lean-pool/lean-pool-0117.lean`

- `(hFC : ∀ t, ‖F t‖ ≤ C)` (theorem): Continuity of F gives a bound on the compact set of inputs t − τ for t near any fixed t₀ and τ between 0 and T. Use that local bound in place of hFC in the dominated-integral continuity argument; for T < 0 the integrand vanishes throughout the interval. Thus the conclusion holds without a global bound.
- `(hC : 0 ≤ C)` (theorem): It follows from hFC by taking t = 0 and using 0 ≤ ‖F 0‖ ≤ C, so it can be derived from the other hypotheses.
- `(hT : 0 ≤ T)` (theorem): If T < 0, the interval from 0 to T lies where τ ≤ 0, and mildShiftedStokesIntegrand is zero there by definition. The integral is therefore zero for every t and hence continuous. For T ≥ 0, the stated continuity argument applies.

### [`ESS.buGaussian_shifted_trace_strip_tendsto`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUGaussianAverageTools.lean#L334-L436) — `lean-pool-0118`

Snippet: `samples/lean-pool/lean-pool-0118.lean`

- `(hB : MeasurableSet B)` (theorem): The identity of the integrals and hence the tendsto conclusion hold for arbitrary B. `setIntegral_parabolic_to_product` and `MeasurePreserving.setIntegral_image_emb` do not require the integrated set to be measurable. The proof uses hB only to apply `setIntegral_congr_ae`; those two congruences can instead use the integrands' pointwise equality and equality of integrals under function equality, which needs no measurability of B. The integrals over a nonmeasurable B are still well-defined set integrals, so this does not rely on excluding a degenerate case.

### [`PDL.localInterpolantStep_oneSidedR`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/Local.lean#L307-L366) — `lean-pool-0128`

Snippet: `samples/lean-pool/lean-pool-0128.lean`

- `(def_rule : rule = LocalRule.oneSidedR orule YS_def)` (theorem): This equality follows from the type of `rule` and the other arguments. In `LocalRule`, the only constructor compatible with source `(∅, Rcond, none)` is `oneSidedR`: `oneSidedL` would require an empty one-sided precondition, ruled out by `OneSidedLocalRule.precond_ne_nil`; the contradiction and loaded constructors have incompatible indices. Matching the result index with `ress_1` and `YS_def` identifies the constructor’s result data, and `OneSidedLocalRule` values with the same precondition are subsingleton (`oneSidedLocalRuleSubsingleton`). Thus `def_rule` can be derived and deleted. These index arguments also cover empty finsets; there is no degenerate constructor exception.

### [`GerverSofa.PartC.Stage2.rhoC_nonneg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MovingSofa/GerverSofa/KernelOnly/Core/Bundle006.lean#L896-L906) — `lean-pool-0129`

Snippet: `samples/lean-pool/lean-pool-0129.lean`

- `(ht : t ∈ Set.Icc (0 : ℝ) T)` (theorem): The claim holds for every real t, so this range assumption can be deleted. In the first rhoC branch the value is 1/2, and in the final branch it is 0. In the phase-2 branch, not hφ gives params.phi < t; `Romik.phi_pos_of_mem_box params_mem` then gives 0 ≤ t, enough for `rhoC_phase2_nonneg`. In phase 3, not hθ gives params.theta < t, and the checked bound `theta_lower_crude` gives 0 ≤ t, enough for `rhoC_phase3_nonneg`. In phase 4, the branch conditions give eta ≤ t and t ≤ tau, exactly the hypotheses of `rhoC_phase4_nonneg`, which derives t ≥ 0 itself. Thus neither endpoint of the Icc assumption is needed, including for degenerate or junk values of t.

### [`AVenhance.Infra.Section5.Contracts.sds_gradMatrix_entry_periodic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/Contracts/TermCenteredAnalyticSmooth.lean#L49-L57) — `lean-pool-0130`

Snippet: `samples/lean-pool/lean-pool-0130.lean`

- `(hF : Differentiable ℝ F)` (theorem): The equivariance hypothesis alone implies that each scalar component at `x + latticeShift k` is obtained from the component at `x` by translating the input and adding a constant to the output. Translation preserves Fréchet differentiability in both directions, and when the derivatives exist they agree; when they do not, `fderiv` is zero at both points. Thus the periodicity conclusion holds without global differentiability. The proof can establish this componentwise directly from `he`, without using `hF`. No degenerate case is excluded by removing it.

### [`RS.LaurentTail.injG_apply_of_not_mem`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/LaurentTail/Comparison.lean#L1239-L1247) — `lean-pool-0131`

Snippet: `samples/lean-pool/lean-pool-0131.lean`

- `[T1Space X]` (variable): The separate T1 instance can be deleted: `[T2Space X]` already provides `T1Space X` via Mathlib's `T2Space.t1Space` instance (in `Mathlib/Topology/Separation/Hausdorff.lean`, lines 115–117). Thus any T1 instance needed while elaborating the statement or proof is synthesized from the remaining T2 assumption; the proof itself uses only `hnot` and the definition of `injG`.

### [`polytopeRoundedSupportCurve_regular`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OperatorTheory/Operator/Crouzeix/SmoothSupportCurve.lean#L231-L242) — `lean-pool-0133`

Snippet: `samples/lean-pool/lean-pool-0133.lean`

- `(hu : u.Nonempty)` (theorem): Split on whether `u` is empty. If nonempty, the given proof applies. If empty, the partition sum is zero, so `Real.log 0 = 0` makes `polytopeSoftSupport` zero and `polytopeRoundedSupport` the constant `rho`. Its support curve is regular because its curvature radius is `rho > 0`; apply `smoothSupportCurve_regular` to the constant function `rho`. Thus the conclusion also holds in the empty-set case without `hu`.

### [`QuadraticCarleson.packetPoint_abs_sub_right_ge`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/CounterexampleGeometry.lean#L68-L86) — `lean-pool-0135`

Snippet: `samples/lean-pool/lean-pool-0135.lean`

- `(hN : 100 ≤ N)` (theorem): The conclusion holds for every integer k, independently of N: split on 0 ≤ k. In the nonnegative case, Int.toNat_of_nonneg identifies k.toNat with k and the bound on j plus τ < 1/2 gives the estimate. In the negative case, Int.toNat is 0 (Lean core defines it as 0 on negative integers), so j ≥ 1; the distance is j − k − τ, which is at least 1 − τ > 1/2, while the left side is j − 1 + 1/2. Thus the proof can use this split without hN.
- `(hk : k ∈ paperBohrIndices N)` (theorem): As with hN, this membership assumption is only used by the proof's auxiliary cast lemma; it is not needed for the estimate. For arbitrary k, split on 0 ≤ k and use Int.toNat_of_nonneg in that case, while for k < 0 use Int.toNat_of_nonpos to get k.toNat = 0. The given j bound and τ < 1/2 then yield the stated inequality in either case.

### [`NavierStokes.PhysicalCoordinateBounds.xLift_homogeneous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalCoordinateBounds.lean#L421-L426) — `lean-pool-0136`

Snippet: `samples/lean-pool/lean-pool-0136.lean`

- `(_hy : y ∈ positiveTime)` (theorem): The proof body does not use `_hy`, and the identity holds for arbitrary `y`, including when `y.1 = 0`: for `r > 0`, `r ≠ 0`, so the numerator and denominator factors of `r` cancel. The proof goes through unchanged without this binder. The positivity assumption on `r` cannot likewise be deleted: at `r = 0`, the left side is `0 / 0 = 0` while the right side is generally `xLift y`. 

### [`NavierStokes.ActivationCone.natural_reference_bounds`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ActivationCone.lean#L819-L863) — `lean-pool-0138`

Snippet: `samples/lean-pool/lean-pool-0138.lean`

- `(hδlim : 2 * δ < ReferencePath.rampLimit)` (theorem): The bound only needs to hold on some initial interval, and its width τ may be chosen smaller than both δ and rampLimit. On that interval the continuation agrees locally with the natural profiles: in the defining primitive, slopeCutoff is 1 up to δ, and the natural profiles are smooth below rampLimit. Thus the proof can use local smoothness and the natural-profile slope and cone-margin estimates, then apply the compact bounds argument on a sufficiently small interval; it need not require 2 * δ < rampLimit. This works for every positive δ, including δ beyond the ramp limit, because τ can shrink independently.

### [`NavierStokes.TerminalStress.swirlCoefficient_contDiffAt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalStress.lean#L412-L420) — `lean-pool-0158`

Snippet: `samples/lean-pool/lean-pool-0158.lean`

- `(hh1 : h < 1 / 2)` (theorem): If this bound is removed, split on whether h < 1/2. In the first case the existing `flattening_contDiffAt` argument applies. Otherwise, since hh gives h > 0, `2 * h < 1` is false, so the defining conditional for `SimilarityCoordinates.coordinateQ` selects its fallback value 1 at every point. Thus `SimilarityProfile.X h p = p.2.1`, and the flattening is smooth by composing hf with the smooth logarithm of the positive second coordinate (hs). The physicalHeat and denominator arguments are unchanged, so the conclusion still follows; the boundary h = 1/2 is covered by the same fallback.

### [`PDL.LoadedCluster.satDown_three_not_basic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/ClusterSatDown.lean#L575-L602) — `lean-pool-0171`

Snippet: `samples/lean-pool/lean-pool-0171.lean`

- `(hlen : next.length = (C.stepOfL Δ).length)` (theorem): The proof uses `hlen` only to turn `hi : i < (C.stepOfL Δ).length` into the bound needed by `IH`. But `hlab i hi` says `labelAt (x ++ [i])` is `some ...`; by `QuasiTab.atOpt_append` and `hx`, this implies that `i` is a valid child index in `next`, hence `i < next.length`. So the proof can obtain `hi'` from `hlab i hi` and `hx` instead. The statement remains true without `hlen`; the degenerate case of an out-of-range child cannot satisfy `hlab`.

### [`NavierStokesAndEuler.SmoothCutoff.cutoff_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/ForMathlib/SmoothCutoff.lean#L86-L90) — `lean-pool-0181`

Snippet: `samples/lean-pool/lean-pool-0181.lean`

- `(hR : 0 < R)` (theorem): If R ≤ 0, hx and 0 ≤ ‖x‖ force R = 0 and ‖x‖ = 0, hence x = 0. Then cutoff E 0 0 = baseCutoff E 0 = 1 by unfolding cutoff and applying baseCutoff_eq_one (since ‖0‖ ≤ 1). For R < 0, hx is impossible. Thus the result holds without hR; the proof can split on 0 < R and handle the other case as above.

### [`BooleanIsoperimetry.harper_macaulay_min`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L154-L176) — `lean-pool-0191`

Snippet: `samples/lean-pool/lean-pool-0191.lean`

- `(ha : a ≤ 2 ^ N)` (theorem): If `a ≤ 2 ^ N`, the original strong-induction proof applies without needing `ha` as an assumption: this inequality is available in that case. Otherwise, `H_mono`, `H_full`, and `H_le_cube` from `Cube.lean` give `H N a = 2 ^ N`. Then the right side is at least `2 ^ N + a ≥ 2 ^ (N + 1)`, while `H_le_cube` bounds the left side by `2 ^ (N + 1)`. Thus the result holds without `ha`, including the out-of-range case.
- `(hb : b ≤ 2 ^ N)` (theorem): By symmetry, split on whether `b ≤ 2 ^ N`. In that case the original strong-induction proof applies with this bound available; otherwise `H_mono`, `H_full`, and `H_le_cube` give `H N b = 2 ^ N`. The right side is then at least `b + 2 ^ N ≥ 2 ^ (N + 1)`, and `H_le_cube` bounds the left side by `2 ^ (N + 1)`. So `hb` can also be deleted.

### [`PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PebblingLean/UpperBoundParameters.lean#L2099-L2138) — `lean-pool-0205`

Snippet: `samples/lean-pool/lean-pool-0205.lean`

- `(hsmall : splitM K n < n)` (theorem): This follows from `hslack`, so the proof can first derive it and then proceed unchanged. If `n = 0`, `loss n = 0`, contradicting `hslack`. If `n = 1`, `Real.log 1 = 0`, hence `splitM K n = 0 < n`. For `n ≥ 2`, failure of `hsmall` gives `splitM K n ≥ n`, so `splitA K n = n - splitM K n = 0`; then `hslack` would imply `1 ≤ loss n = 1/(n : ℝ)^2 ≤ 1/4`, a contradiction.

### [`AleksandrovDifferentiability.prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/AleksandrovDifferentiability/Analysis/GoodSet.lean#L97-L106) — `lean-pool-0218`

Snippet: `samples/lean-pool/lean-pool-0218.lean`

- `(hs : MeasurableSet s)` (theorem): The conclusion still follows without measurability of `s`. From `hbad`, choose a measurable set `t ⊆ s \ G` that is ae-equal to `s \ G`. For each `x`, the section `tₓ` is measurable and lies in the section of `s` outside `G`. The section hypothesis makes that bad part null under `ν.restrict {y | (x,y) ∈ s}`; since `tₓ` is measurable and contained in the restricting set, `Measure.restrict_apply` identifies its restricted measure with `ν(tₓ)`, so `ν(tₓ) = 0`. Fubini applied to measurable `t` gives `(μ.prod ν) t = 0`, and the ae equality from `hbad` gives the desired result. This argument does not require `s` or its sections to be measurable.

### [`Zeta5Irrational.cov_302_304`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta5Irrational/Table/Intervals.lean#L7296-L7302) — `lean-pool-0219`

Snippet: `samples/lean-pool/lean-pool-0219.lean`

- `0 < t` (theorem): The lower bound `(723732917263 / 2560000000000 : ℝ) ≤ t` already implies `0 < t`, since that rational is positive. Thus the positivity argument can be derived from the lower bound and supplied to `tc_302` or `tc_303`; the explicit positivity hypothesis can be deleted.

### [`TauCeti.DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_reducingSubspace`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/SinTheta/Natural/Reducing.lean#L496-L543) — `lean-pool-0223`

Snippet: `samples/lean-pool/lean-pool-0223.lean`

- `(hAdense : Dense (A.domain : Set ER))` (theorem): Self-adjointness `hA` implies density of `A.domain` (`hA.dense_domain`). The proof can use that derived fact wherever density is needed, so this assumption can be deleted, including in degenerate cases.
- `(hAclosed : A.IsClosed)` (theorem): Self-adjointness `hA` implies that `A` is closed (`hA.isClosed`). A proof can use this derived fact instead, so this assumption can be deleted.
- `(hA0dense : Dense (A0.domain : Set FR))` (theorem): Self-adjointness `hA0` implies density of `A0.domain` (`hA0.dense_domain`). A proof can use that derived fact wherever density is needed, so this assumption can be deleted.
- `(hA0closed : A0.IsClosed)` (theorem): Self-adjointness `hA0` implies that `A0` is closed (`hA0.isClosed`). A proof can use this derived fact instead, so this assumption can be deleted.

### [`BGS.CorvajaZannier.exists_support_direction_of_not_rankTwo`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveSupportRank.lean#L186-L216) — `lean-pool-0224`

Snippet: `samples/lean-pool/lean-pool-0224.lean`

- `(hnonsingleton : ∃ s ∈ f.support, s ≠ r)` (theorem): If this hypothesis holds, the existing argument applies. Otherwise, `hr` and its negation imply every `t ∈ f.support` equals `r`, so every `planeExponentDifference r t` is zero. Choose the nonzero vector `(1, 0)` and `k = 0`; the conclusion follows. This also covers the singleton-support case, while `hr` rules out empty support.

### [`ViscositySolns.SmoothConvexApproximationOnInteriorClosedBallTheorem.of_extensionMollification`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Jensen/ConvexMollification.lean#L285-L308) — `lean-pool-0232`

Snippet: `samples/lean-pool/lean-pool-0232.lean`

- `(hmoll : ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem n)` (theorem): The conclusion can be proved without assuming hmoll: first use `exists_continuous_extension_eqOn_intermediate_closedBall_of_convexOn_closedBall` to obtain a continuous extension agreeing with g on a ball of intermediate radius, then construct the mollified sequence directly. The construction in `ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem.proof` (MainTheorems.lean) supplies the needed method using the bump-convolution approximation, differentiability, and convexity lemmas; it does not require hmoll as an assumption. The argument applies also in dimension n = 0, and the radius hypotheses ensure the intermediate-radius and support bounds needed for the construction.

### [`CarlsonFunctions.SeveralComplexVariables.norm_sub_le_of_separately_analytic_bounded`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CarlsonFunctions/SeveralComplexVariables/LocallyBounded.lean#L67-L108) — `lean-pool-0237`

Snippet: `samples/lean-pool/lean-pool-0237.lean`

- `(hr : 0 < r)` (theorem): The conclusion also holds when `hr` is deleted. If `r < 0`, `hx` and `hy` are impossible since distances are nonnegative. If `r = 0`, membership in `closedBall c 0` forces `x = c` and `y = c` coordinatewise, so `x = y` and the left side is zero; the right side is zero as well because real division gives `M / 0 = 0`. Thus the degenerate cases are covered without `hr`.

### [`LeanPool.Besicovitch.sigma_mul_radius_div_two_le_diam_localAttachmentComponent`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Besicovitch/Rectifiability/ComponentDiameter.lean#L38-L191) — `lean-pool-0244`

Snippet: `samples/lean-pool/lean-pool-0244.lean`

- `(hsigma_one : sigma < 1)` (theorem): The proof uses this only to establish `sigma * rho / 2 < rho`. That inequality follows instead from `hannulus`: choose `w` in the annulus. Then `dist z w < rho`, while `w ∉ Metric.ball z (sigma * rho / 2)` gives `sigma * rho / 2 ≤ dist z w`; hence `sigma * rho / 2 < rho`. This also covers the degenerate cases: if the inner radius is at least `rho`, the annulus is empty, contradicting `hannulus`. The rest of the proof can proceed unchanged.

### [`EulerTransversePacketProvider.Forcing.velocityPath_reflection_neg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/TransversePacketParity.lean#L374-L380) — `lean-pool-0247`

Snippet: `samples/lean-pool/lean-pool-0247.lean`

- `(hM : ∀ t x, D.M.field t (-x) = D.M.field t x)` (variable): The theorem needs the frame derivative to be even, but this follows from hF without assuming hM: differentiate the equality D.F.field t (-x) = D.F.field t x in time, using D.frame_time to identify the derivatives with D.F₁.field t (-x) and D.F₁.field t x. Applying the coefficient definition then gives evenness of D.frameDerivative. That replaces the use of D.frameDerivative_even hF hM in the proof. The other parity inputs hSym, hraw, and hinit are not supplied by this argument.

### [`Zeta5Irrational.tc_361`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta5Irrational/Table/Intervals.lean#L2671-L2676) — `lean-pool-0249`

Snippet: `samples/lean-pool/lean-pool-0249.lean`

- `(0 < t)` (theorem): The lower bound `(46687825988961 / 128000000000000 : ℝ) ≤ t` already implies `0 < t`, since the rational lower bound is positive (`norm_num` proves this). Without the positivity premise, derive it from the lower-bound premise by transitivity and use the existing proof.

### [`CKN.norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Poincare/Lp.lean#L159-L202) — `lean-pool-0254`

Snippet: `samples/lean-pool/lean-pool-0254.lean`

- `[MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]` (theorem): This instance can be recovered from `hvol`: positivity of `(volume U).toReal` implies `volume U < ⊤` (by `ENNReal.toReal_pos_iff`), and the restricted measure has total mass `volume U`. Thus the proof can install the finite-measure instance locally. This also handles the zero-volume case, which `hvol` excludes.
- `(hu : MeasureTheory.IntegrableOn u U)` (theorem): With the finite-measure instance obtained from `hvol`, the constant function `u x` is integrable on `U`. The pointwise segment estimate `norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment huDiff x y` bounds `‖u x - u y‖` by the integrable function supplied by `hsegment`. Since `huDiff` makes `u` continuous and hence strongly measurable, domination gives integrability of `u x - u y`, and subtracting it from the integrable constant function gives `IntegrableOn u U`. That derived integrability supplies the hypothesis needed by the existing average estimate; no degenerate case is lost.

### [`EGZ.CommonMeasure.final_mass_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ErdosGinzburgZiv/EGZ/Decomposition/CommonMeasure.lean#L109-L119) — `lean-pool-0276`

Snippet: `samples/lean-pool/lean-pool-0276.lean`

- `(hε : 0 < ε)` (theorem): The conclusion holds for ε ≤ 0 without this hypothesis: `hu` gives nonnegative `mass u P` and `mass u Q` (by `WeightedIncidence.mass_nonneg`), so the left side is ≤ 0 and the right side is ≥ 0. For ε > 0, the branch supplies `hε` and the existing proof via `relative_mass_le` and `mass_mono` applies.

### [`eigenvector_constant_sign`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SpectralPositivity/Operator/JentzschProof.lean#L332-L387) — `lean-pool-0280`

Snippet: `samples/lean-pool/lean-pool-0280.lean`

- `(hT_compact : IsCompactOperator T)` (theorem): The conclusion can be proved without compactness. The only use of `hT_compact` is passing it to `abs_eigenvector_of_top_eigenvector`; that lemma declares the corresponding parameter `_hT_compact` and does not use it in its proof. Its proof relies instead on self-adjointness, positivity preservation, the eigenvector assumptions, and the top bound. Removing that unused parameter from the lemma and its call leaves the proof of this theorem unchanged. No degenerate case requires compactness.

### [`QuadraticCarleson.annularQuadraticKernel_correlation_le_ordered`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/QuadraticFixedHeightAveragingCorrelation.lean#L49-L127) — `lean-pool-0281`

Snippet: `samples/lean-pool/lean-pool-0281.lean`

- `(hS : 0 < S)` (theorem): It follows from hR : 0 < R and hRS : R ≤ S. Removing hS leaves all other assumptions and the conclusion unchanged.
- `(hH : 0 < H)` (theorem): Since hu gives u > 0, u^5 > 0; hdecay gives 1 ≤ H * u^5, hence H > 0. Thus hH can be deleted without changing the statement.
- `(hD : 0 ≤ D)` (theorem): From hab at any t, 0 ≤ ‖a t‖ ≤ D / R. As hR gives R > 0, this implies D ≥ 0. Thus hD can be deleted; the remaining assumptions provide the nonnegativity used in the proof.

### [`AVenhance.Infra.Section3.ChiMKCorrector.chiMK_spaceLap_three_active`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section3/ChiMKCorrector.lean#L159-L209) — `lean-pool-0282`

Snippet: `samples/lean-pool/lean-pool-0282.lean`

- `(hk : k % 4 = 3)` (theorem): The same eigenfunction identity holds for every `k`: `ChiMKCorrector.chiMK_component_spaceLap_eigen` proves it for all components, and this conclusion is its `j = 0` instance. When `k % 4 = 3`, component 0 is active; otherwise `chiMK` component 0 is zero, so both sides vanish. Thus the proof can be replaced by that general theorem without `hk`.

### [`Malliavin.memLp_mderiv_cylinder_expGrowth`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/CylindricalGrowth.lean#L488-L496) — `lean-pool-0295`

Snippet: `samples/lean-pool/lean-pool-0295.lean`

- `(hC : 0 ≤ C)` (theorem): This follows from `hfg'`: evaluate it at the zero vector in `Fin n → ℝ`; the derivative norm is nonnegative and `Real.exp (c * ‖0‖) = 1`, so `0 ≤ C`. The proof can use this derived fact wherever `hC` was used. This also works for `n = 0`.
- `(hc : 0 ≤ c)` (theorem): For `c < 0`, `‖y‖ ≥ 0` gives `Real.exp (c * ‖y‖) ≤ 1`; using `hC`, `hfg'` therefore bounds the derivative by the constant `C`. Apply `memLp_mderiv_cylinder_of_dominated` with the constant dominating function and its integrable square (the Gaussian measure is finite). For `c ≥ 0`, the existing exponential-growth proof applies. Thus the sign assumption can be removed without changing the statement, including at zero or in dimension zero.

### [`Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_of_generated`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/BrownianPurePowerDuality.lean#L393-L402) — `lean-pool-0298`

Snippet: `samples/lean-pool/lean-pool-0298.lean`

- `(hsm : ∀ t, StronglyMeasurable (B t))` (theorem): This can be derived from `coordinate_apply`: each `coordinate t` is continuous, and with `[BorelSpace W]` and `[SecondCountableTopology W]`, `Continuous.stronglyMeasurable` gives strong measurability of its coercion to a function. Replacing `hsm` in the proof with `fun t => by rw [coordinate_apply]; exact (coordinate t).continuous.stronglyMeasurable` supplies the premise needed by the generated-identity and equivalence lemmas. The conclusion itself does not mention `hsm`; no degenerate-case exception is involved.


## FLT (Anthropic) (61 flagged)

### [`P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.C2idemCore.IdempotentOrbit.exists_idempotent_orbit_or_isField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.lean#L172-L278) — `flt-anthropic-0014`

Snippet: `samples/flt-anthropic/flt-anthropic-0014.lean`

- `[Finite ι]` (theorem): This can be derived from the other hypotheses. The periodicity condition makes `s` invertible (with inverse an iterate), so its conjugate through `φ` is a ring automorphism of the product. A ring automorphism preserves the order on idempotents and hence the minimal nonzero idempotents, which in this product are exactly the singleton indicators; it therefore permutes the coordinates. For any coordinate, its orbit under this permutation is a nonempty finite invariant set. Its indicator, transported back by `φ.symm`, is an idempotent fixed by `s`. By `hfix`, it comes from `k`; an idempotent in a field is 0 or 1, and the field hom is injective, so the transported indicator is 0 or 1. It cannot be 0 because the orbit is nonempty, so it is 1. Thus the finite orbit is all of `ι`, proving `ι` finite. If `ι` is empty, `R` is subsingleton via `φ` and the left disjunct holds as in the proof. Once finiteness is established, the original argument applies. This reasoning also handles the empty and singleton cases.

### [`P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve.CuspDecayOfAux.qL_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.lean#L116-L119) — `flt-anthropic-0016`

Snippet: `samples/flt-anthropic/flt-anthropic-0016.lean`

- `[hTΓ : Fact (ModularGroup.T ∈ Γ)]` (variable): The period hypothesis is only used to apply `ModularForm.qExpansion_add` in the given proof. Unfolding `qL`, the equality is additivity of the raw `qExpansion` coefficients: each coefficient is a factorial scalar times an iterated derivative of `cuspFunction`, and iterated derivatives are additive. Thus it holds for any Γ and needs no period assumption; the strict-period condition is not part of the statement's types.

### [`P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6.comp_heckeDiag_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.lean#L664-L678) — `flt-anthropic-0018`

Snippet: `samples/flt-anthropic/flt-anthropic-0018.lean`

- `(hp : p ≠ 0)` (theorem): When p = 0, `ModularForm.heckeDiagMatrix_zero` says the matrix is 1, whose action on `UpperHalfPlane` is the identity, so the conclusion reduces to `hF`. For p ≠ 0, the existing proof applies. Thus a proof can split on `p = 0`, using `hF` in the zero case and the existing argument in the nonzero case.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node.B25N3.algebraMap_pow_p`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node.lean#L662-L668) — `flt-anthropic-0027`

Snippet: `samples/flt-anthropic/flt-anthropic-0027.lean`

- `[Field κ]` (variable): The statement and proof need only a semiring structure on κ, supplied by the remaining `[CharP κ p]` and `[Algebra ℤ_[p] κ]` assumptions. The existing proof's key step can be reproduced without a field: `map_natCast` followed by `CharP.cast_eq_zero κ p` shows the algebra map kills p. The rest uses the reduction of `a ^ p - a` modulo p (`ZMod.pow_card`) and that p maps to zero, so its image is zero. These arguments also cover trivial target rings if the remaining assumptions permit them; no field-specific case is needed.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.CHRAux.Tr_fixed`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.lean#L97-L99) — `flt-anthropic-0032`

Snippet: `samples/flt-anthropic/flt-anthropic-0032.lean`

- `[DecidableEq G]` (variable): The statement and proof need only `[Fintype G]`: `Tr` is defined as a sum over `G`, and `Fintype.sum_equiv` reindexes that sum using an equivalence without requiring decidable equality. Thus the same proof works when `[DecidableEq G]` is omitted, including for groups without a decidable-equality instance.

### [`P2MW.S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.ModularCurve.RiemannHurwitzCount.not_ord_sub_pos_of_ord_sub_pos`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.lean#L307-L323) — `flt-anthropic-0044`

Snippet: `samples/flt-anthropic/flt-anthropic-0044.lean`

- `(hcc' : c ≠ c')` (theorem): If c = c', the premise h is exactly the negation of the conclusion, so the result follows by contradiction. If c ≠ c', the existing proof applies. Thus a proof without hcc' can split on c = c'; no zero or junk-value case causes a problem, since the equality branch uses only h itself.

### [`P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.P2mS17LB.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.lean#L49-L111) — `flt-anthropic-0046`

Snippet: `samples/flt-anthropic/flt-anthropic-0046.lean`

- `(hn : 0 < n)` (theorem): This follows from the remaining hypothesis `hqn`: if `n = 0`, then `q ∣ n` by `dvd_zero`, contradicting `hqn`. Since `n : ℕ`, nonzeroness gives `0 < n`. The proof can derive `hn` from `hqn` and use that in its existing steps; the statement and conclusion need not change.

### [`P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.PLCDSol.exists_gamma0_apply_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.lean#L883-L889) — `flt-anthropic-0048`

Snippet: `samples/flt-anthropic/flt-anthropic-0048.lean`

- `[NeZero M]` (variable): The claim also holds for M = 0. Then ZMod 0 identifies with ℤ, and for any unit d one can use the diagonal matrix with entries d and d⁻¹: its determinant is 1, its lower-left entry is 0 (so it lies in Gamma0 0), and its upper-left entry reduces to d. For M ≠ 0, the existing proof via CohCarrier.gamma0Units_surjective applies. Thus the instance can be omitted, with a separate diagonal-matrix case for M = 0.

### [`P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.CohCarrier.gammaH_inf_gamma0_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.lean#L104-L128) — `flt-anthropic-0049`

Snippet: `samples/flt-anthropic/flt-anthropic-0049.lean`

- `[NeZero N]` (theorem): This is not needed: the definitions of `GammaH` and `gamma0Units` and the `Gamma0_mem` characterization apply at modulus 0 as well. The displayed proof uses neither nonzeroness assumption, and its cast and units-map arguments still apply when `N = 0`; in that case the target modulus is also 0, and the map induced by `dvd_mul_right N ℓ` is the identity on `ZMod 0`, so both sides agree.
- `[NeZero (N * ℓ)]` (theorem): This is not needed: `GammaH` and `Gamma0` are defined at modulus 0, and the proof uses no nonzeroness assumption. When `N * ℓ = 0` (including `ℓ = 0`), the same cast argument works; the right-hand comap condition says precisely that the unit character at modulus `N` lies in `H'`, alongside the `Gamma0 0` condition, as on the left.

### [`P2MW.S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.ModularCurve.CupPairing.Shapiro.b_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.lean#L287-L288) — `flt-anthropic-0052`

Snippet: `samples/flt-anthropic/flt-anthropic-0052.lean`

- `[Γ.FiniteIndex]` (variable): The conclusion and the type of `P` do not require finite index. The proof uses `b_mul_sub_eq`, which reduces to `a_mul_sub_eq`; those arguments use only the `Potentials` fields and subgroup membership, with no finite-index assumption. Thus the same proof works for any subgroup Γ, including infinite or trivial ones.

### [`TateCurve.pointX_inv_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_TateCurve_XMultStructure.lean#L171-L175) — `flt-anthropic-0057`

Snippet: `samples/flt-anthropic/flt-anthropic-0057.lean`

- `(hu0 : u ≠ 0)` (theorem): If u = 0, both arguments of pointX simplify to 0, so the conclusion follows by simp. If u ≠ 0, use hu0 := hu and the existing pointX_inv proof. Thus hu0 can be removed while retaining the other hypotheses.
- `(hv0 : v ≠ 0)` (theorem): If v = 0, both arguments of pointX simplify to 0, so the conclusion follows by simp. If v ≠ 0, use hv0 := hv and the existing pointX_inv proof. Thus hv0 can be removed while retaining the other hypotheses.

### [`P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.Nat.not_mem_placesOf_of_mem_placesOf_of_coprime`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.lean#L72-L74) — `flt-anthropic-0058`

Snippet: `samples/flt-anthropic/flt-anthropic-0058.lean`

- `(hℓ : ℓ ≠ 0)` (theorem): If ℓ = 0, `placesOf 0` is empty by its definition and `Ideal.span_singleton_eq_bot`, contradicting `hv`. Otherwise ℓ ≠ 0 is available, so the proof can use `disjoint_placesOf_of_coprime` as before.
- `(hℓ' : ℓ' ≠ 0)` (theorem): If ℓ' = 0, `placesOf 0` is empty by its definition and `Ideal.span_singleton_eq_bot`, so the conclusion is immediate. Otherwise ℓ' ≠ 0 is available, so the proof can use `disjoint_placesOf_of_coprime` as before.

### [`P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.lean#L843-L876) — `flt-anthropic-0059`

Snippet: `samples/flt-anthropic/flt-anthropic-0059.lean`

- `(hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)` (theorem): The conclusion does not mention ϖ or hϖ. The proof can choose a normalized uniformizer of the completion instead and use it in the intermediate lemmas. Such an element exists because the valuation on this number-field completion has value group ℤ, so an element of valuation −1 has norm (Ideal.absNorm v.asIdeal : ℝ)⁻¹. This does not require any special case for zero or a trivial type: a height-one spectrum point gives a nontrivial discrete valuation.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L610-L612) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- `[CharZero L]` (variable): The identity holds for fields of any characteristic. The statement and its proof only need `[Field L]`: `algebraMap_laurentSeries_eq_single` uses `[Field L]`, and rewriting with `HahnSeries.C_apply` requires no characteristic-zero assumption. Thus `[CharZero L]` can be omitted without changing the statement.

### [`P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.W8O.ramificationIndex_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.lean#L169-L198) — `flt-anthropic-0064`

Snippet: `samples/flt-anthropic/flt-anthropic-0064.lean`

- `[CharP M p]` (variable): This characteristic assumption follows from [CharP E p]: since M and E are fields, the algebra map M → E is injective, so `charP_of_injective_algebraMap (algebraMap M E).injective p` supplies the instance. Thus, after removing this binder, the proof can install the derived instance locally wherever `theta` or its supporting lemmas need it; the conclusion and all other hypotheses remain unchanged. Injectivity also covers characteristic zero, so there is no exceptional zero-characteristic case.

### [`P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.lean#L2414-L2438) — `flt-anthropic-0066`

Snippet: `samples/flt-anthropic/flt-anthropic-0066.lean`

- `(ha2 : a ^ (q ^ 2) = a)` (theorem): The statement does not otherwise depend on `ha2`, and the proof never uses it: after constructing `θ`, it applies `ModularCurve.C4b.core θ f h₁ h₁F h₁0 a ha hsupp`. The core theorem has no `a ^ (q ^ 2) = a` hypothesis, so the proof and conclusion hold unchanged without `ha2`, including when that equality fails.

### [`P2MW.S_CohCarrier_isEis_kernel_pair_of_prime.CohCarrier.IsEisKernelPairPrime.exists_crt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_isEis_kernel_pair_of_prime.lean#L359-L443) — `flt-anthropic-0072`

Snippet: `samples/flt-anthropic/flt-anthropic-0072.lean`

- `[NeZero P]` (theorem): If P ≠ 0, this follows from the case assumption; if P = 0, Nat.Coprime P M₁ forces M₁ = 1. In that case choose g₁ = g: mapN 0 is the identity and mapN 1 is trivial. Thus a proof can split on P = 0 and use the existing CRT proof otherwise.
- `[NeZero M₁]` (theorem): If M₁ ≠ 0, this follows from the case assumption; if M₁ = 0, Nat.Coprime P M₁ forces P = 1. In that case choose g₁ = 1: mapN 1 is trivial and mapN 0 sends 1 to 1. Thus a proof can split on M₁ = 0 and use the existing CRT proof otherwise.

### [`P2MW.S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.lean#L36-L71) — `flt-anthropic-0083`

Snippet: `samples/flt-anthropic/flt-anthropic-0083.lean`

- `[NeZero N]` (theorem): The statement’s curve types and the proof’s uses of `x1FunctionField N`, `x1FunctionFieldBar N`, and `JOne N` are defined for every natural number N; they do not require N to be nonzero. The proof uses no nonzeroness fact about N, so it works unchanged for N = 0 as well.

### [`P2MW.S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.Loc4Sol.residual_isEquiv_point`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.lean#L165-L200) — `flt-anthropic-0088`

Snippet: `samples/flt-anthropic/flt-anthropic-0088.lean`

- `(hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)` (theorem): This is only used to infer `¬ ℓ ∣ N` for primes outside `S`. Without it, enlarge the finite exclusion set passed to `GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq` to include both `S` and the primes dividing `N`. Outside that set, the hypotheses `hθ`, `hρ'`, and `ha` apply directly, so the same Frobenius comparison and residual-representation equivalence proof goes through. The excluded primes are finite; this also works when `N = 1`, and the context already excludes `N = 0`.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.K45VolB3.iterate_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.lean#L218-L220) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- `[NumberField L]` (variable): The statement only needs L to be a field with the displayed K-algebra structure; NumberField L is not needed to form σE, the tensor product, or the theorem’s types. The proof uses sigmaTensor_pow and map_mul, which require no NumberField L assumption. Thus the identity remains valid for any field L satisfying the other assumptions; no degenerate-value exception is involved.

### [`P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD.pairF_res_cores_normal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_index_Gamma_four.lean#L5591-L5659) — `flt-anthropic-0095`

Snippet: `samples/flt-anthropic/flt-anthropic-0095.lean`

- `(hΦ1 : (-1 : SL(2, ℤ)) ∉ Φ)` (theorem): This follows from `[IsFreeGroup Φ]`: a free group is torsion-free, while `-1` in `SL(2, ℤ)` is nonidentity and has square `1`. The Mathlib source defines `IsFreeGroup` via an equivalence with a `FreeGroup` and proves free groups have unique roots in `FreeGroup/CyclicallyReduced.lean`. Thus the proof can derive `hΦ1` from the free-group instance and use it at `pairF_transport`; the conclusion itself is unchanged.

### [`P2MW.S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.lean#L99-L202) — `flt-anthropic-0099`

Snippet: `samples/flt-anthropic/flt-anthropic-0099.lean`

- `(hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)` (theorem): The proof does not use `hcover`, and it is not needed to elaborate the conclusion. Deleting it leaves the proof unchanged; no degenerate cases arise because the result is independent of this hypothesis.
- `(hred : IsReduced (pullback i₁.1 i₂.1))` (theorem): The proof does not use `hred`, and it is not needed to elaborate the conclusion. Deleting it leaves the proof unchanged; no degenerate cases arise because the result is independent of this hypothesis.

### [`P2MW.S_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units.NodeAddEquiv.phi_some`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units.lean#L81-L82) — `flt-anthropic-0103`

Snippet: `samples/flt-anthropic/flt-anthropic-0103.lean`

- `[CharZero L]` (variable): The statement uses `Field L` for its operations, but `CharZero L` is not needed to state or prove this definitional equality. After deleting this instance argument, `rfl` still unfolds `phi` and reduces the unit coercion to the displayed fraction; no degenerate case is excluded.
- `[DecidableEq L]` (variable): `DecidableEq L` is not needed by the statement: `Nonsingular` is defined using the curve equation and polynomial nonvanishing, and `Point.some` merely stores such a proof. Although `Point` has a derived `DecidableEq` instance, this statement does not use it. Deleting the instance argument leaves the proof by `rfl` unchanged.

### [`P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.R4GC.qC_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.lean#L1440-L1442) — `flt-anthropic-0104`

Snippet: `samples/flt-anthropic/flt-anthropic-0104.lean`

- `[NeZero m]` (variable): The statement’s types do not require `m ≠ 0`: `Γ m M'` and `qC` are defined without that instance. The proof uses `ModularForm.qExpansion_eq_zero_iff`, which requires only `one_pos` and `one_mem_strictPeriods`; the latter is proved from `translation_mem_GammaH` and does not require `NeZero m`. Thus the equivalence remains valid, including at `m = 0`, without this hypothesis.

### [`P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.R3M4Torus.ι₀_root`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.lean#L48-L49) — `flt-anthropic-0111`

Snippet: `samples/flt-anthropic/flt-anthropic-0111.lean`

- `[Fact (Irreducible γ₀.charpoly)]` (variable): The theorem takes this instance because its type mentions γ₀, but neither the type of ι₀ nor AdjoinRoot.root requires irreducibility: ι₀ is defined using the quotient lift and the matrix charpoly identity. The proof `rw [AdjoinRoot.root, ι₀_mk, Polynomial.aeval_X]` also does not use the instance, so it proves the same statement without it.

### [`P2MW.S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.lean#L32-L223) — `flt-anthropic-0121`

Snippet: `samples/flt-anthropic/flt-anthropic-0121.lean`

- `(hθ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), θ t = θ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))` (theorem): The proof never refers to `hθ` (the only other occurrences of that name are in `hθ'U`). The conclusion and the types of the remaining binders do not depend on it, so the existing proof establishes the same result after deleting this binder; no degenerate cases need separate treatment.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.M4aD2Skeleton.zetaIntegral_eq_setIntegral_theta'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.lean#L6363-L6392) — `flt-anthropic-0122`

Snippet: `samples/flt-anthropic/flt-anthropic-0122.lean`

- `(hD'm : MeasurableSet D')` (theorem): `hD'` already supplies `NullMeasurableSet D' ν` via the `nullMeasurableSet` field of `IsFundamentalDomain`. The proof uses `hD'm` only for the final set-integral congruence; replacing `setIntegral_congr_fun hD'm` with `setIntegral_congr_fun₀ hD'.nullMeasurableSet` proves the same pointwise congruence. This also covers degenerate sets such as the empty set.

### [`P2MW.S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.NumberField.AdelicFourier.GodementSiegelEstimate.real_bound`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.lean#L337-L423) — `flt-anthropic-0123`

Snippet: `samples/flt-anthropic/flt-anthropic-0123.lean`

- `(hC : 0 ≤ C)` (theorem): This can be deleted by setting C' = max C 0 and using the original proof with C' in place of C; C' is nonnegative, so its required hypothesis holds. The expression multiplying C on the left is nonnegative (including when N = 0), and C ≤ C', so the resulting bound also bounds the original left-hand side. This covers C < 0 as well, with the original left-hand side nonpositive.

### [`P2MW.S_TateCurve_ks17_D3_exports.TateCurve.sum_mul_Fz_Fz_eq_sum_lines_nat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_ks17_D3_exports.lean#L108-L111) — `flt-anthropic-0124`

Snippet: `samples/flt-anthropic/flt-anthropic-0124.lean`

- `[IsUltrametricDist K]` (theorem): The identity is a finite-sum reindexing and uses only field operations and `Fz u 0 = 0`; it has no dependence on the metric. The source’s `sum_mul_Fz_eq_sum_lines_nat` is proved under only `[NontriviallyNormedField K]`, and the two-index identity follows by finite fiberwise grouping. Thus this instance can be deleted while retaining the other assumptions.
- `[CompleteSpace K]` (theorem): The identity is a finite-sum reindexing and uses only field operations and `Fz u 0 = 0`; it has no dependence on completeness. The source’s `sum_mul_Fz_eq_sum_lines_nat` is proved under only `[NontriviallyNormedField K]`, and the two-index identity follows by finite fiberwise grouping. Thus this instance can be deleted while retaining the other assumptions.

### [`P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.MapsDvdSol.opFamily_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.lean#L343-L365) — `flt-anthropic-0134`

Snippet: `samples/flt-anthropic/flt-anthropic-0134.lean`

- `[IsDomain 𝒪]` (variable): The statement and the commutation proof require only the commutative-ring/module structure on 𝒪. `opFamily` uses Hecke operators on `H1`, and `heckeT_comm_of_prime` proves the needed commutation for an additive group without assuming that the coefficient ring is a domain. Thus this instance can be omitted while retaining the other hypotheses.
- `[CharZero 𝒪]` (variable): Neither the statement nor the proof uses characteristic zero: the operator commutation lemma applies to the underlying additive group, with no characteristic assumption. The conclusion therefore remains provable after omitting this instance.
- `[IsLocalRing 𝒪]` (variable): The statement and proof need only the commutative-ring/module structure on 𝒪; `heckeT_comm_of_prime` has no local-ring assumption. The conclusion remains provable without this instance.

### [`P2MW.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.ModularCurve.map_eval₂_aeval_toRingHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.lean#L18-L24) — `flt-anthropic-0137`

Snippet: `samples/flt-anthropic/flt-anthropic-0137.lean`

- `[Algebra ℤ A]` (theorem): `[CommRing A]` supplies `[Ring A]`, which has the canonical `Ring.toIntAlgebra` instance. `Algebra ℤ A` is subsingleton (`int_algebra_subsingleton`), so this is the only possible algebra structure. Thus the statement and proof can use the inferred instance instead; this also works for the zero ring.
- `[Algebra ℤ B]` (theorem): `[CommRing B]` supplies `[Ring B]`, which has the canonical `Ring.toIntAlgebra` instance. `Algebra ℤ B` is subsingleton (`int_algebra_subsingleton`), so this is the only possible algebra structure. Thus the statement and proof can use the inferred instance instead; this also works for the zero ring.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.C2Count.natCard_finPts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.lean#L214-L257) — `flt-anthropic-0143`

Snippet: `samples/flt-anthropic/flt-anthropic-0143.lean`

- `(hm : 0 < m)` (theorem): This follows from `hmp` and `[Fact p.Prime]`: if `m = 0`, then `m.Coprime p` would force `p = 1`, contradicting that `p` is prime. Thus the proof can derive `hm` and use it in the same steps; the conclusion is unchanged.

### [`P2MW.S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.K51A1.retr_tmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.lean#L38-L40) — `flt-anthropic-0160`

Snippet: `samples/flt-anthropic/flt-anthropic-0160.lean`

- `[FiniteDimensional K L]` (variable): The tensor-product computation in the proof needs no finite-dimensionality, and the statement remains well-typed and true without this instance; the same `rw` proof applies.
- `[IsTopologicalRing A]` (variable): Neither the statement nor the proof uses the topological-ring structure. Removing it leaves the other binders, including `[TopologicalSpace A]`, in place, and the same `rw` proof applies.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.R4ODGlue.eq_of_proj_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.lean#L415-L421) — `flt-anthropic-0167`

Snippet: `samples/flt-anthropic/flt-anthropic-0167.lean`

- `hcomm` (variable): The commutativity assumption can be omitted. Apply `hpb` to `(0, 0)`, which is compatible since ring homomorphisms send zero to zero; uniqueness then shows that the only element whose two projections are zero is zero. If `b₁` and `b₂` have equal projections, their difference has both projections zero, so it is zero and `b₁ = b₂`. This also works for degenerate rings.

### [`P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.KcSemiLocalIwasawaHaar.coe_nGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.lean#L1038-L1038) — `flt-anthropic-0168`

Snippet: `samples/flt-anthropic/flt-anthropic-0168.lean`

- `[NumberField L]` (variable): The instance is automatically included because its type mentions `L`, which is already an argument, but the conclusion only uses `L` as a field in the tensor product and matrix group. `NumberField.Basic.lean` defines `NumberField` as a proposition over an already-given field, and `AutomorphicForm.unipotentGL2` in `Def_AutomorphicForm_ConstantTerm.lean` requires only a commutative ring. Thus the equality remains true without assuming that `L` is a number field; the existing definitional proof `rfl` still works. The other field and algebra assumptions remain available, so the statement still elaborates.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.AlgebraicCurve.AlgebraicCurve.adeleBddPrincipal_eq_comap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean#L791-L793) — `flt-anthropic-0183`

Snippet: `samples/flt-anthropic/flt-anthropic-0183.lean`

- `[HasPrincipalDivisors K F]` (theorem): The definitions of `adeleBddPrincipal` and `globalSub` do not require this instance. The equality follows from the submodule identity `(A ⊔ G).comap C.subtype = A.comap C.subtype ⊔ G.comap C.subtype` whenever `A ≤ C`, taking `A := adeleBdd D` and `C := adeleSpace K F`. For the reverse inclusion, decompose an element of `C ∩ (A ⊔ G)` into an `A` part and a `G` part; since the `A` part is in `C`, the `G` part is in `C` as well. This avoids needing `globalSub K F ≤ adeleSpace K F`, which is the only reason the existing proof requires the instance. The argument is purely about submodules, so it also covers degenerate cases.

### [`P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE.ell_sub_eq_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.lean#L175-L187) — `flt-anthropic-0184`

Snippet: `samples/flt-anthropic/flt-anthropic-0184.lean`

- `(hf0 : f ≠ 0)` (theorem): If f = 0, then Place.ord_zero gives v.ord f = 0 for every v. Thus hP forces P = 0 pointwise, so E - P = E and the conclusion follows directly. In the f ≠ 0 case, the existing proof applies unchanged.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf.Rebase.e0_smulB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.lean#L392-L398) — `flt-anthropic-0192`

Snippet: `samples/flt-anthropic/flt-anthropic-0192.lean`

- `[IsSeparated q]` (variable): The theorem’s statement and proof use `q`, but not separatedness. The types of `GW`, `e0`, and the cochain do not require `[IsSeparated q]`; the proof uses the restriction map’s scalar compatibility and the definitions of `e0` and `GW_smul_def`. Thus the same identity and proof go through without this instance, including degenerate cases.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.eq_span_tInvChart_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L2727-L2734) — `flt-anthropic-0199`

Snippet: `samples/flt-anthropic/flt-anthropic-0199.lean`

- `(ht : Transcendental κ t)` (variable): Although `ht` is included in the theorem, it can be removed by splitting on whether `t` is transcendental. In the transcendental case, use `eq_span_of_pow_mem` with `transcendental_inv κ t ht` as in the proof. In the algebraic case, `t⁻¹` is nonzero and algebraic, so its inverse `t` is a polynomial in `t⁻¹`; `hchartInv` then puts `t` in the chart ring. Thus `tInvChart κ t` is a unit, and no proper prime ideal can contain it, making the conclusion vacuous. The existing `Fact (t ≠ 0)` handles the zero case.

### [`P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.RoadA.coe_τ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.lean#L325-L326) — `flt-anthropic-0219`

Snippet: `samples/flt-anthropic/flt-anthropic-0219.lean`

- `[NeZero M]` (variable): The instance can be omitted: `modularFunctionFieldBar` is defined as a Laurent-series base change, and `arithmeticRingAut` (used by `τ`) does not require `NeZero` for its input field. Thus the statement still elaborates without the instance, and the equality remains `rfl`; the case `M = 0` is included as well.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.R4TateModelKHb.Xc_def`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.lean#L362-L362) — `flt-anthropic-0230`

Snippet: `samples/flt-anthropic/flt-anthropic-0230.lean`

- `[CharZero L]` (variable): The statement mentions L, so the instance-implicit variable [CharZero L] is included as an argument. It is not needed: the equality is definitional (`rfl`), and the statement’s operations are supported by [Field L] alone. Removing [CharZero L] leaves the statement elaborable and the same proof works.

### [`P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc.Bdd.mul_small`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PowerSeries_dvd_of_forall_taylorShift_order_le.lean#L132-L135) — `flt-anthropic-0231`

Snippet: `samples/flt-anthropic/flt-anthropic-0231.lean`

- `(hC : 0 ≤ C)` (theorem): This follows from `hP`: by `Bdd`'s definition, `‖coeff 0 P‖ ≤ C`, and a norm is nonnegative. Thus one can derive `0 ≤ C` and use the same multiplication argument. This deletion is independent of deleting `hC'`.
- `(hC' : 0 ≤ C')` (theorem): This follows from `hQ`: evaluating `Small` at `k = m` gives `‖coeff m Q‖ ≤ C' * ρ ^ 0 = C'`, so norm nonnegativity yields `0 ≤ C'`. Thus one can derive it and use the same multiplication argument. This deletion is independent of deleting `hC`.

### [`P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.EtaleCoordK1a.rankAtStalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean#L13-L24) — `flt-anthropic-0236`

Snippet: `samples/flt-anthropic/flt-anthropic-0236.lean`

- `[Module.FinitePresentation S M]` (theorem): This is used only to apply the locally-constant-rank lemma in the given proof. For any prime p, the same localization-rank argument used at ⊥ works directly: since S is a domain, p.asIdeal.primeCompl consists of nonzero elements and is contained in nonZeroDivisors S. Apply IsLocalization.rank_eq and IsLocalizedModule.rank_eq to get rank of the localized module equal to hrank, then Module.finrank_eq_of_rank_eq gives the stated equality. The latter lemma requires only the rank equality, not finite presentation.
- `[Module.Flat S M]` (theorem): Flatness is used only for the locally-constant-rank step in the given proof. As above, for each p the localization-rank equalities directly identify the stalk's rank with Module.rank S M; this proof works without flatness, including at every prime of the domain.

### [`P2MW.S_ModularCurve_NodeLocalized_exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint.PowerSeries.Submodule.COMP.θ_X_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_NodeLocalized_exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint.lean#L806-L808) — `flt-anthropic-0237`

Snippet: `samples/flt-anthropic/flt-anthropic-0237.lean`

- `[Fact (Irreducible ϖ)]` (variable): The theorem only uses ϖ to form the quotient W ϖ and the maps θ₀, θW, θ₁, and θ₂; their definitions and the X-zero computation do not require ϖ to be irreducible. The quotient by the ideal generated by X − C ϖ and the displayed ring-map identities are defined for any ϖ, so the same proof works after omitting this instance.

### [`P2MW.S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.SupersingularTop3.mem_of_ord_nonneg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.lean#L40-L46) — `flt-anthropic-0240`

Snippet: `samples/flt-anthropic/flt-anthropic-0240.lean`

- `(hf : f ≠ 0)` (theorem): The case `f = 0` also satisfies the conclusion: `Place.ord_zero` gives `w.ord 0 = 0`, and zero belongs to `w.toValuationSubring`. Split on `f = 0`; in the nonzero case the existing proof applies using the resulting inequality and the `hf` obtained from the split.

### [`WeierstrassCurve.zero_mem_kernelIdealSet`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_KernelIdeal.lean#L16-L19) — `flt-anthropic-0246`

Snippet: `samples/flt-anthropic/flt-anthropic-0246.lean`

- `[DecidableEq k]` (variable): The statement does not require decidable equality on `k`: `IsRationallyRepresented` and `rationalHomSet` are defined without using it, and `rationalEndSubring` and `kernelIdealSet` only build on those definitions. The witness remains `0`, using `zero_mem_rationalHomSet`; the zero-composition equality is unchanged. This argument also works for empty or trivial types, since it uses no elements of `k` or equality decisions on them.

### [`P2MW.S_RubinSilverberg_exists_polynomial_rsFamily.M4cP2.D52.PhiA_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_RubinSilverberg_exists_polynomial_rsFamily.lean#L410-L414) — `flt-anthropic-0247`

Snippet: `samples/flt-anthropic/flt-anthropic-0247.lean`

- `(hj : j < 21)` (theorem): The two sides, viewed as polynomials in the parameter `t`, have degree at most 20: `lhsPairAG` uses fifth powers of linear expressions in `t`, and the `hornerG` term is built from the 21-entry `tabA` list. For each fixed `s < 197`, `gridA` gives equality at `t = 0, …, 20`; the degree bound and the same finite-evaluation root argument used in this theorem then give equality for every `t`, including `j ≥ 21`. Applying the existing 197-point evaluation argument in `X` proves the stated polynomial equality without `hj`. This works over `ℤ` without an excluded zero or other degenerate case.

### [`P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.R4RRN.FF_slash_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.lean#L366-L368) — `flt-anthropic-0250`

Snippet: `samples/flt-anthropic/flt-anthropic-0250.lean`

- `[NeZero M']` (variable): The local `Γ` is defined as `GH q M'`, and its definition requires `[NeZero q]` but not `[NeZero M']`; the statement and the rewrite proof likewise need no nonzero assumption on `M'`. In particular, `M' = 0` causes no issue: the theorem still follows by the displayed slash-action rewrites. Thus `[NeZero M']` can be omitted while leaving the statement unchanged.

### [`P2MW.S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.AlgebraicCurve.AlgebraicCurve.Place.stichtenothGenusExists_of_isFractionRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean#L2159-L2166) — `flt-anthropic-0261`

Snippet: `samples/flt-anthropic/flt-anthropic-0261.lean`

- `[Algebra.IsSeparable E F]` (variable): Separability is not needed to construct the pole-divisor package: the integral-basis step uses `FiniteDimensional.exists_is_basis_integral` (Mathlib's `IntegralClosure.lean`), which requires finite dimensionality but not separability; finite dimensionality also supplies integrality for the regular-outside argument. The pole-divisor degree calculation uses the tower's degree hypothesis, not separability. Thus the package and the genus-existence conclusion can be proved without this instance, including for inseparable finite extensions. The other hypotheses, including `[FiniteDimensional E F]`, remain in place.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.WeierstrassCurve.WeierstrassCurve.ModularCurve.kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean#L3405-L3408) — `flt-anthropic-0263`

Snippet: `samples/flt-anthropic/flt-anthropic-0263.lean`

- `[WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F).toAffine]` (variable): This instance does not occur in the theorem statement and is not used by its proof: the proof applies `Transcendental.of_tower_top` to `transcendental_polyToFunctionField_X`. Neither requires a `GenusOnePlaceGate` instance, so this argument can be omitted.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]` (variable): This instance does not occur in the theorem statement and is not used by its proof, which applies `Transcendental.of_tower_top` to `transcendental_polyToFunctionField_X`. Omitting it leaves the statement and that proof unchanged.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]` (variable): This instance does not occur in the theorem statement and is not used by its proof, which applies `Transcendental.of_tower_top` to `transcendental_polyToFunctionField_X`. Omitting it leaves the statement and that proof unchanged.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F').toAffine]` (variable): This instance does not occur in the theorem statement and is not used by its proof: `transcendental_polyToFunctionField_X` supplies the transcendence over `F'`, and `Transcendental.of_tower_top` then gives the result over `F`. Neither step requires a `GenusOnePlaceGate` instance.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]` (variable): This instance does not occur in the theorem statement or the proof. The proof uses only `transcendental_polyToFunctionField_X` and `Transcendental.of_tower_top`, which do not require a centred gate.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]` (variable): This instance does not occur in the theorem statement or the proof. The proof uses only `transcendental_polyToFunctionField_X` and `Transcendental.of_tower_top`, which do not require an `AbelTheorem` instance.

### [`P2MW.S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.lean#L203-L596) — `flt-anthropic-0267`

Snippet: `samples/flt-anthropic/flt-anthropic-0267.lean`

- `(hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)` (theorem): This follows from the other hypotheses. For a prime q dividing N, if q = p then p ∈ S follows from hpSmin and hSmin. If q ≠ p, hN.2 gives q ∈ Smin, hence q ∈ S by hSmin. The proof can derive this helper fact and use it in place of hNS wherever needed; no degenerate case is excluded.

### [`P2MW.S_Function_orbitCensus_of_dihedralThree_relations.P2MKcOrbitCensus.b_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean#L14-L17) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- `[Fintype X]` (variable): The theorem and its proof do not use finiteness. Removing this instance leaves the statement unchanged, and the proof from hb still establishes injectivity; on an empty type injectivity holds trivially as well.
- `[DecidableEq X]` (variable): The theorem and its proof do not use decidable equality. Removing this instance leaves the statement unchanged, and the proof from hb still establishes injectivity; on an empty type injectivity holds trivially as well.

### [`P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.UqNSol.fstDiv_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean#L358-L366) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- `[hqN : Fact (¬ q ∣ N)]` (variable): `hqN` is not needed to form `PlaceSpecialization` (its definition requires primality and `NeZero N`, but not `q ∤ N`) or the divisor types in the statement. The proof only uses finite-sum induction and `fstDiv_add`; it can be carried out unchanged without this instance.

### [`P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.CerednikDrinfeld.BrandtLevel.mem_modOf_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.lean#L566-L575) — `flt-anthropic-0272`

Snippet: `samples/flt-anthropic/flt-anthropic-0272.lean`

- `[IsAlgClosed κ]` (variable): The statement and proof do not need algebraic closedness: the rationalHomSet definition uses Field and DecidableEq, and the proof is just the map-membership equivalence for modOf followed by unpacking the subgroup subtype. The same proof works over any field κ with the other assumptions; there is no exceptional empty or trivial case.

### [`P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.LCMazur.OrdQ.span_singleton_eq_range_ordProj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.lean#L263-L272) — `flt-anthropic-0275`

Snippet: `samples/flt-anthropic/flt-anthropic-0275.lean`

- `[Module.Finite A V]` (variable): The hypothesis `h2 : finrank A V = 2` implies `Module.Finite A V` in the presence of `[Module.Free A V]`: Mathlib's `Module.finite_of_finrank_eq_succ` gives finiteness from a positive successor finrank. After deleting this instance argument, the proof can install the derived instance locally from `h2` and then use the existing proof unchanged. The statement still elaborates without it because `finrank` here only requires the free-module instance.

### [`P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.lean#L27-L40) — `flt-anthropic-0278`

Snippet: `samples/flt-anthropic/flt-anthropic-0278.lean`

- `(ha : a ≠ 0)` (theorem): The equivalence also holds when `a = 0`: `μ 0 = 0 < 1`, and the zero element belongs to `IsLocalRing.maximalIdeal A`. For `a ≠ 0`, the existing proof applies unchanged. Thus a proof without this binder can split on `a = 0`, use these facts in that case, and use the existing argument otherwise.

### [`P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.TH1Wanted2.inv_mem_and_const_mem_of_gaussPresentation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.lean#L874-L964) — `flt-anthropic-0285`

Snippet: `samples/flt-anthropic/flt-anthropic-0285.lean`

- `(hq3 : q = 3)` (theorem): This hypothesis occurs nowhere else in the statement or proof. The proof works for arbitrary q, so deleting it leaves the statement and proof unchanged; no special case such as q = 0 is used.
- `(hqM' : ¬ q ∣ M')` (theorem): This hypothesis occurs nowhere else in the statement or proof. Deleting it leaves the statement and proof unchanged, including when q divides M'.
- `(hK₁ : FiniteDimensional ↥k₀ ↥K₁)` (theorem): This hypothesis is not used in the statement or proof: the argument only uses K₁, A₁, and hA₁, and does not require K₁ to be finite-dimensional. Deleting it leaves the proof applicable without additional degenerate-case assumptions.

### [`P2MW.S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.P2mConormLSpace.CFE.trace_algebraMap'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.lean#L193-L203) — `flt-anthropic-0287`

Snippet: `samples/flt-anthropic/flt-anthropic-0287.lean`

- `[Algebra.IsSeparable K K']` (variable): This can be removed while retaining `[FiniteDimensional K K']`. The condition `hconst` says that every element of F algebraic over K lies in the image of K, so F/K is regular and hence linearly disjoint from every algebraic extension of K, including K'. Using any K-basis of K' (rather than the separable power basis used in this proof), its image is an F-basis of F' by linear disjointness and `hgen`. The multiplication matrices for `algebraMap K' F' k` are then scalar extensions of those for k, so their traces give the stated identity. This also covers trivial or inseparable K'/K; no separability assumption is needed.

### [`P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.lean#L110-L138) — `flt-anthropic-0294`

Snippet: `samples/flt-anthropic/flt-anthropic-0294.lean`

- `[IsDomain A]` (theorem): This instance follows from the other assumptions: `IsFractionRing.isDomain_iff_isField` gives `IsDomain A ↔ IsField K`, and `[Field K]` supplies the right-hand side. After deleting the binder, the proof can locally install the resulting `IsDomain A` instance and proceed unchanged. The field assumption rules out the degenerate zero-ring case.

### [`P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.WNormSwapSol.θ_θ_γel`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.lean#L941-L962) — `flt-anthropic-0295`

Snippet: `samples/flt-anthropic/flt-anthropic-0295.lean`

- `hζ : IsPrimitiveRoot ζ p` (variable): The conclusion is independent of the choice of primitive root. Without this included variable, choose a primitive p-th root in `Qb = AlgebraicClosure ℚ`: Mathlib provides `HasEnoughRootsOfUnity.exists_isPrimitiveRoot`, and the algebraic closure of ℚ has enough roots of unity for every nonzero p. Since `Fact p.Prime` ensures p ≠ 0, this applies even at the smallest prime p = 2. Converting the chosen root to a unit supplies the witness used in `map_μ_eq`; the rest of the proof then proceeds with that choice. The root-separation argument remains valid for any primitive root.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.AlgebraicCurve.DiscRigidity.sum_filter_eq_of_degreeOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.lean#L80-L105) — `flt-anthropic-0299`

Snippet: `samples/flt-anthropic/flt-anthropic-0299.lean`

- `(hf : f ≠ 0)` (theorem): The case f = 0 also satisfies the conclusion: `Place.ord_zero` gives `v.ord 0 = 0` for every v, so hDf forces Df = 0; its support is empty and both sums are zero. Thus the proof can split on f = 0, handle that case directly, and use the existing proof in the nonzero case.


## Formal Frontier (15 flagged)

### [`GradedRing.Veronese.adjoin_component_one_eq_top`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseDegreeOne.lean#L80-L104) — `formal-frontier-0005`

Snippet: `samples/formal-frontier/formal-frontier-0005.lean`

- `(hn : 0 < n)` (theorem): The theorem also holds when n = 0. Then every summand of VeroneseRing 𝒮 0 has coefficient type 𝒮 0; the summand at index 0 is the base component, and each summand at index j > 0 is generated by products of elements from component 𝒮 0 1 (use coefficient a in one degree-one factor and coefficient 1 in the other j−1 factors). Thus the conclusion holds without hgen in this case. For n > 0, the proof proceeds as given, retaining hn for eval_mem_adjoin and zeroRingEquiv.

### [`ProjectiveSpace.finrank_homogeneousSubmodule_fin`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/HomogeneousDimension.lean#L58-L65) — `formal-frontier-0115`

Snippet: `samples/formal-frontier/formal-frontier-0115.lean`

- `[StrongRankCondition R]` (variable): The statement itself only needs `[CommSemiring R]`. The same proof works without the strong rank condition: the homogeneous-component equivalence to a supported Finsupp module and `Module.finrank_finsupp_self` require no such condition; the latter follows from the general `CommSemiring.rank_self`. The remaining cardinality and arithmetic steps are independent of `R`. This also covers degenerate rings, including the zero semiring, since the cited rank result holds for commutative semirings generally.

### [`Nat.DivisionGrowth.affine_lower_bound`](https://github.com/FormalFrontier/sequence-growth/blob/7b7db3df8a043a09d037de4ff1eced6873404fb2/SequenceGrowth/Data/Nat/DivisionGrowth.lean#L68-L94) — `formal-frontier-0117`

Snippet: `samples/formal-frontier/formal-frontier-0117.lean`

- `(hs : 0 < s)` (theorem): The theorem remains true without this binder by splitting on s. If s > 0, the existing proof applies. If s = 0, hsn gives n > 0; then s - 1 = 0, the offset is 0, and (n : ℚ) / s = 0. For m = 0 the conclusion is equality, and for m > 0 its left side is 0, which is at most (u m : ℚ). Thus this case needs neither hs nor hstep.

### [`ContinuousGroupCohomology.LevelCompact.finiteTateNegative_eq_positiveHomology`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/CompactNegativeTate.lean#L372-L381) — `formal-frontier-0134`

Snippet: `samples/formal-frontier/formal-frontier-0134.lean`

- `[IsTopologicalGroup G]` (variable): This instance is not needed to form `OpenNormalSubgroup G`, `LevelCompact A`, or either side of the equality. `LevelCompact` and `continuous_quotientToInvariants_action` are defined with only `[Group G]` and `[TopologicalSpace G]`; the theorem remains definitional by `rfl` without this instance.
- `[CompactSpace G]` (variable): This instance is not needed to form `OpenNormalSubgroup G`, `LevelCompact A`, or either side of the equality. The compactness used by `finiteTateNegative` is supplied by `L.compact` for the coefficient invariants, not by compactness of `G`; the theorem remains definitional by `rfl` without this instance.

### [`AlgebraicGeometry.matrixStdBasis_dual_apply`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/MatrixEndAdditive.lean#L70-L77) — `formal-frontier-0140`

Snippet: `samples/formal-frontier/formal-frontier-0140.lean`

- `[DecidableEq (m × n)]` (theorem): `Matrix.stdBasis` only requires `[Fintype m]`, `[Finite n]`, and `[Semiring K]`; its `dualBasis` is available because `m × n` is finite. Neither `Module.Basis.dualBasis_apply` nor `matrixStdBasis_repr` requires decidable equality. Thus the identity remains provable without this instance.

### [`IsKrasner.adjoin_rootSet_le_adjoin_rootSet_of_norm_coeff_sub_lt`](https://github.com/FormalFrontier/polynomial-root-stability/blob/ceae7822f6151ec6626678db1653054d3398cff3/PolynomialRootStability/Krasner.lean#L363-L391) — `formal-frontier-0152`

Snippet: `samples/formal-frontier/formal-frontier-0152.lean`

- `(hε : 0 < ε)` (theorem): The coefficient bound at index 0 gives ‖g.coeff 0 - f.coeff 0‖ < ε, while a norm is nonnegative; hence 0 < ε follows from hcoeff. After deleting hε, derive it this way and use it in the proof. This also shows the coefficient-bound hypotheses cannot hold in the degenerate case ε ≤ 0.

### [`Subgroup.exists_continuous_coset_representative`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ContinuousCosetRepresentative.lean#L55-L74) — `formal-frontier-0160`

Snippet: `samples/formal-frontier/formal-frontier-0160.lean`

- `[T2Space G]` (variable): A totally disconnected space is T0: distinct inseparable points would form a non-singleton preconnected subset, contradicting total disconnectedness. For a topological group, T0 implies T2 (Mathlib’s `IsTopologicalGroup.t2Space_of_one_sep` gives the group separation step). Thus the remaining assumptions supply T2 without this argument, and the continuous-section theorem used in the proof can still be applied. This does not rely on excluding the trivial-group case.

### [`MvPowerSeries.isUnit_adicallyRestricted_iff_coeff_radical`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean#L83-L92) — `formal-frontier-0162`

Snippet: `samples/formal-frontier/formal-frontier-0162.lean`

- `[IsAdicComplete I R]` (variable): The criterion can be proved without completeness. For each k, the image of a restricted series modulo I^k is a polynomial, by the definition of `adicallyRestrictedSubring`. If its nonconstant coefficients lie in `I.radical`, the finitely many nonconstant coefficients of that polynomial are nilpotent modulo I^k, so its nonconstant part is nilpotent; its constant coefficient is a unit. Thus the polynomial is a unit. Conversely, a unit in the restricted subring maps modulo I to a unit polynomial, whose nonconstant coefficients are nilpotent, giving radical membership. The inverse polynomial reductions show that the formal inverse is restricted. This also covers degenerate ideals and zero quotients; completeness is only used in the displayed proof to reflect scalar units from R ⧸ I.

### [`AlgebraicGeometry.isIntegrallyClosed_stalk_of_specializes`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/Normal.lean#L279-L308) — `formal-frontier-0174`

Snippet: `samples/formal-frontier/formal-frontier-0174.lean`

- `[_root_.IsDomain (X.presheaf.stalk y)]` (theorem): A scheme stalk is a local ring, and an integrally closed local ring is a domain. Thus the remaining hypothesis `[_root_.IsIntegrallyClosed (X.presheaf.stalk y)]` supplies this domain property, so the explicit domain assumption can be removed; the localization argument then applies unchanged. The stalk at a scheme point is nontrivial, so there is no zero-ring exception.

### [`GradedRing.Veronese.finiteType_of_finiteType`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseFiniteType.lean#L105-L126) — `formal-frontier-0179`

Snippet: `samples/formal-frontier/formal-frontier-0179.lean`

- `(hn : 0 < n)` (theorem): The result also holds at the omitted case n = 0: `GradedRing.Veronese.finiteType_zero` proves `Algebra.FiniteType (component 𝒮 0 0) (VeroneseRing 𝒮 0)` without any finiteness assumption. For n > 0, recover `hn` from n and use the existing proof. Thus a proof without this binder can split on n; the zero case is covered by `finiteType_zero`, and the positive case by the stated argument.

### [`AlgebraicGeometry.Proj.degreeScaledChartMap_preimage_basicOpen`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/DegreeScaledMap.lean#L453-L469) — `formal-frontier-0188`

Snippet: `samples/formal-frontier/formal-frontier-0188.lean`

- `(hr : r ∈ 𝒜 n)` (theorem): The equality holds for arbitrary r, not just homogeneous r. Decompose r into its graded components and use `Proj.basicOpen_eq_iSup_proj` to reduce the equality to the componentwise basic-open preimage; the degree-zero component is handled by the induced degree-zero ring map. Thus hr can be deleted while retaining hn.
- `(hn : 0 < n)` (theorem): The equality holds for arbitrary r, including homogeneous elements of degree zero. The positivity requirement is used by the cited `awayι_preimage_basicOpen` proof, not by the equality itself: reduce arbitrary r to its graded components with `Proj.basicOpen_eq_iSup_proj`, treating degree zero via the induced degree-zero ring map. Thus hn can be deleted while retaining hr.

### [`finiteGroupPresentation_iff_compact_totallyDisconnected`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/FiniteGroupCharacterization.lean#L198-L214) — `formal-frontier-0200`

Snippet: `samples/formal-frontier/formal-frontier-0200.lean`

- `[T2Space G]` (theorem): This can be deleted: in a topological group, total disconnectedness gives `connectedComponent (1 : G) = {1}` by `totallyDisconnectedSpace_iff_connectedComponent_one`. Connected components are closed (`isClosed_connectedComponent`), so `{1}` is closed; `IsTopologicalGroup.t2Space_iff_one_closed` then supplies the T2 instance. In the reverse direction, install that instance from `hdisconnected` before applying `ProfiniteGrp.of G`; the forward direction needs no T2 instance.

### [`AlgebraicGeometry.Scheme.Hom.ker_radical_of_isReduced_source`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L154-L160) — `formal-frontier-0232`

Snippet: `samples/formal-frontier/formal-frontier-0232.lean`

- `[QuasiCompact f]` (theorem): The proof uses quasi-compactness only to rewrite `f.ker.ideal U` as the full componentwise ring-hom kernel via `f.ker_apply`. Without it, `f.ker.ideal U ≤ RingHom.ker (f.app U).hom` still holds by `Hom.ideal_ker_le`. Since `[IsReduced X]` makes the source affine sections reduced, this ring-hom kernel is `⊥`; hence every component of `f.ker` is `⊥`, so `f.ker = ⊥` and its radical is also `⊥`. This argument does not require quasi-compactness, including in degenerate cases.

### [`MonomialOrder.restrictedResidue_support_eq_of_unit_factor`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LeadingTerm.lean#L502-L543) — `formal-frontier-0258`

Snippet: `samples/formal-frontier/formal-frontier-0258.lean`

- `[ValuationRing R]` (variable): The statement and proof use only commutative-ring operations, ideal quotients, and the adically restricted subring, whose definition requires only `[CommRing R]`. The coefficientwise proof works without valuation-ring properties. Keeping `[IsDomain R]` while deleting this instance still lets the statement elaborate; the degenerate cases are covered by the same coefficientwise argument.

### [`MvPowerSeries.existsUnique_firstVariable_division_of_scalar_top`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableDivision.lean#L112-L132) — `formal-frontier-0285`

Snippet: `samples/formal-frontier/formal-frontier-0285.lean`

- `(hc : c ≠ 0)` (theorem): It follows from the other hypotheses. Primitivity `hprim` ensures the residue polynomial is nonzero: `restrictedLeadingExponent_eq_degree_of_primitive_reduction` derives a unit content coefficient and the corresponding nonzero residue support. For a nonzero polynomial, `natDegree = d` implies its coefficient at `d` is nonzero, including when `d = 0`. Then `htop` says this coefficient is `MvPolynomial.C c`, so injectivity of the constant-polynomial map gives `c ≠ 0`. Thus the zero-polynomial edge case at degree zero is excluded by `hprim`, and the proof can derive `hc` before applying `lex_degree_of_finSuccEquiv_scalar_top`.

