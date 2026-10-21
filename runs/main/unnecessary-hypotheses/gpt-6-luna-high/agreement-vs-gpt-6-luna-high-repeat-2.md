# Test-retest: `gpt-6-luna-high-repeat-2` vs `gpt-6-luna-high`, run `main`

The second pass judged each theorem in a fresh session, without the first verdict.

| Library | Flags re-flagged | Non-flags flagged | Same hypothesis | κ |
|---|---:|---:|---:|---:|
| Mathlib | 7/11 (35%–85%) | 5/289 (1%–4%) | 7/7 | 0.59 |
| Tau Ceti | 12/18 (44%–84%) | 7/282 (1%–5%) | 12/12 | 0.63 |
| Lean Pool | 43/51 (72%–92%) | 5/249 (1%–5%) | 38/43 | 0.84 |
| FLT (Anthropic) | 44/60 (61%–83%) | 17/240 (4%–11%) | 41/44 | 0.66 |
| Formal Frontier | 11/15 (48%–89%) | 4/285 (1%–4%) | 11/11 | 0.72 |

Overall κ: 0.73 (on the 1500 theorems judged by both passes).

## Mathlib: 9 disagreements

### [`Module.Basis.toMatrix_mulVec_repr`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Matrix/Basis.lean#L231-L236) — `mathlib-0083`: flagged first, not again

- `[Finite ι']`: The statement only needs `[Fintype ι]` for the matrix-vector product; it does not require the row index type `ι'` to be finite. Without `[Finite ι']`, prove the equality by extensionality on `ι'`, expand `mulVec` and `Basis.toMatrix`, and use the finite basis expansion `b.sum_repr m` followed by the linear map `b'.repr` to identify each coordinate. This argument works for arbitrary `ι'` and does not rely on a nonempty or nontrivial index type.

### [`Unitization.cobounded_eq_aux`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Algebra/Unitization.lean#L195-L198) — `mathlib-0113`: flagged first, not again

- `[NormedSpace 𝕜 A]`: The bornology equality is independent of the scalar normed-space structure. The `Unitization` bornology is induced by `addEquiv`; its definition and the conclusion use only the additive structures already supplied by the other assumptions. The equality can be proved by reflexivity, including in degenerate cases.
- `[IsScalarTower 𝕜 A A]`: The bornology equality is independent of the scalar tower structure. The `Unitization` bornology is induced by `addEquiv`, so the conclusion can be proved by reflexivity without this assumption.
- `[SMulCommClass 𝕜 A A]`: The bornology equality is independent of this scalar-action commutation property. The `Unitization` bornology is induced by `addEquiv`, so the conclusion can be proved by reflexivity without it.
- `[RegularNormedAlgebra 𝕜 A]`: Although this assumption is used by the Lipschitz proof in the file, the bornology equality itself is just the equality between `cobounded` for the induced bornology and for `Unitization`'s bornology, which is defined as `Bornology.induced (addEquiv 𝕜 A)`. The conclusion can therefore be proved by reflexivity without the regularity assumption, even in degenerate cases.

### [`HomologicalComplex.pOpcycles_extendOpcyclesIso_inv`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Homology/Embedding/ExtendHomology.lean#L372-L383) — `mathlib-0257`: flagged first, not again

- `[(K.extend e).HasHomology j']`: The extension homology instance is derivable from `[K.HasHomology j]` and `hj'`: `extend` has an instance at `e.f j` from `[K.HasHomology j]` (line 285 of `ExtendHomology.lean`), and `hj'` identifies `e.f j` with `j'`. Thus this variable can be omitted while the statement's required instance is synthesized.

### [`ProbabilityTheory.Kernel.withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Kernel/RadonNikodym.lean#L336-L367) — `mathlib-0258`: flagged first, not again

- `(hsm : MeasurableSet s)`: The measures agree after restricting to the measurable set `(mutuallySingularSetSlice κ η a)ᶜ`: for any measurable test set, apply this theorem to its intersection with that complement, which is measurable. Equality of the restricted measures then gives equality on arbitrary `s` contained in the complement, since evaluating a restricted measure on `s` does not require `s` itself to be measurable. Thus `hsm` can be removed; the finite-kernel assumptions remain available for establishing the restricted-measure equality.

### [`Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L275-L280) — `mathlib-0027`: flagged only second

- `[NormedAddCommGroup E]`: `InnerProductSpace 𝕜 E` already supplies the `SeminormedAddCommGroup E` structure needed for the statement and proof. The projection and inner-product lemmas used here require that seminormed structure, not the stronger `NormedAddCommGroup`; removing this variable leaves the theorem statement elaborated and the same proof works.

### [`Convex.norm_image_sub_le_of_norm_fderiv_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/MeanValue.lean#L498-L504) — `mathlib-0148`: flagged only second

- `[NontriviallyNormedField 𝕜]`: This assumption follows from `[IsRCLikeNormedField 𝕜]`: use `IsRCLikeNormedField.rclike 𝕜` and `RCLike.norm_ofReal` at `2` to exhibit an element of norm greater than `1`, yielding a `NontriviallyNormedField` instance. The theorem can retain its statement unchanged and locally install that instance before applying the existing mean-value argument. This also covers the scalar field’s normed structure; no degenerate case is excluded.

### [`Submodule.norm_sq_eq_add_norm_sq_starProjection`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L607-L610) — `mathlib-0170`: flagged only second

- `[NormedAddCommGroup E]`: This supplies more structure than the theorem needs. `InnerProductSpace 𝕜 E` already carries a `SeminormedAddCommGroup E` instance, which suffices for the norm notation and the Pythagorean identity; the identity and the projection argument do not require norm separation. Thus the result remains true with the same statement after dropping this variable, including in degenerate seminormed inner product spaces. The existing proof proceeds via `norm_sq_eq_add_norm_sq_projection` and `norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero`, neither of which requires `NormedAddCommGroup E`.

### [`Set.sub_mem_Ico_iff_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Interval/Set/Group.lean#L98-L99) — `mathlib-0180`: flagged only second

- `[PartialOrder α]`: The equivalence only needs a preorder: the two conjuncts are rearranged using the order-translation facts `sub_lt_comm` and `le_sub_comm`, which do not use antisymmetry. `IsOrderedAddMonoid α` already has a `[Preorder α]` parameter, so the statement's intervals and inequalities remain available without `[PartialOrder α]`; the proof is unchanged.

### [`MeasureTheory.VectorMeasure.ennrealVariation_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/VectorMeasure/Variation/Basic.lean#L60-L62) — `mathlib-0192`: flagged only second

- `(hs : MeasurableSet s)`: The equality also holds when `s` is not measurable: `toENNRealVectorMeasure_apply` gives `μ.ennrealVariation s = 0` in that case, and a vector measure's value on a nonmeasurable set is zero, so `μ.variation s = 0` as well. Thus the measurability argument can be deleted; the measurable case is exactly `toENNRealVectorMeasure_apply_measurable`.

## Tau Ceti: 13 disagreements

### [`RootPairing.coroot'_nonpos_of_mem_negRoots`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/Chamber.lean#L325-L331) — `tauceti-0007`: flagged first, not again

- `[IsDomain R]`: The nonnegative-coroot expansion used in the proof needs no domain assumption: expand the positive root for `P.flip` using `exists_root_eq_sum_nat_of_mem_posRoots`, use `posRoots_flip`, and transport the equality through the coroot linear map. The resulting sum has natural-number coefficients, so `Finset.sum_nonneg` and `nsmul_nonneg` prove nonnegativity. The domain assumption is only used by `exists_coroot'_eq_sum_nat_of_mem_posRoots` to additionally show that some coefficient is nonzero; that fact is unnecessary here. Reflecting the negative root and negating the inequality then gives the stated result. This argument also covers the case where every coefficient is zero.

### [`TauCeti.cohomologicalDimensionAt_eq_of_isOpen_of_ne_top`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/CohomologicalDimension/OpenSubgroup.lean#L108-L115) — `tauceti-0009`: flagged first, not again

- `[TotallyDisconnectedSpace G]`: This can be deleted: for a compact topological group, an open subgroup has finite index, and the finite-index coinduction/trace argument gives the reverse inequality when `cohomologicalDimensionAt p G ≠ ⊤`; the closed-subgroup inequality gives the other direction. The argument does not require total disconnectedness. The other hypotheses are needed: without compactness, for example, `ℤ` with its discrete topology and its open trivial subgroup have dimensions 1 and 0; without `hU`, a closed trivial subgroup of `ℤ_p` gives dimensions 0 and 1; and the finite-dimension assumption is essential as the file’s `ℤ/p` example indicates.

### [`TauCeti.rightTrace_biprod`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/CategoryTheory/Monoidal/Pivotal/Biproduct.lean#L114-L125) — `tauceti-0163`: flagged first, not again

- `[MonoidalPreadditive C]`: This instance is used by the displayed proof for additivity of whiskering and `rightTrace_add`, but it can be removed for this theorem. Since `C` is rigid, tensoring by a fixed object has adjoints and preserves any biproduct that exists. In particular, the needed whiskering preserves the given binary biproduct; the biproduct decomposition and cyclicity of `rightTrace` then prove the stated diagonal formula without assuming global additivity of tensoring. The other assumptions still provide the category, trace, preadditive hom addition, and biproduct notation required by the statement.

### [`TauCeti.FiniteTypeCommHopfAlgCat.range_identityComponentPointsHom`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/AlgebraicGroup/Connected/GroupScheme.lean#L242-L250) — `tauceti-0173`: flagged first, not again

- `[IsAlgClosed k]`: The statement’s types and the definitional equality proved by `rfl` do not depend on algebraic closedness. The identity-component point map is defined as `quotientPointsHom`, and its range reduces definitionally to `quotientPointsSubgroup`; the same `rfl` proof works without this instance. The `Field k` assumption remains available for the other types in the statement.

### [`TauCeti.IsGradedExtInternallyFinite.shiftSourceInverse`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Homology/EulerCharacteristic/ExtEuler/Graded/Shift.lean#L304-L308) — `tauceti-0229`: flagged first, not again

- `[e.functor.Additive]`: An equivalence between abelian categories preserves finite biproducts, and addition of morphisms is determined by the biproduct diagonal and codiagonal. Thus `e.functor` is additive even without this instance; locally supplying that instance lets the existing proof use `gradedExtShiftSourceInverse`. This also holds in degenerate or zero categories.

### [`TauCeti.mem_integralWeightLattice_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/WeightLattice.lean#L194-L199) — `tauceti-0234`: flagged first, not again

- `[FiniteDimensional K L]`: The statement and proof do not require finite dimensionality: `integralWeightLattice` has carrier `IsIntegralWeight`, whose definition quantifies over `Weight K H L` and uses `IsKilling.coroot`, with no `[FiniteDimensional K L]` requirement. Thus `Iff.rfl` still proves the equivalence after omitting this variable.

### [`TauCeti.AffineDynkinType.not_module_finite_preprojectiveAlgebra`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Quiver/Preprojective/InfiniteDimensional.lean#L279-L288) — `tauceti-0002`: flagged only second

- `[Fintype V]`: The theorem’s graph vertices are `Fin t.nodes`, which are finite without this supplied `Fintype` instance. The local `Fintype.ofFinite` instance can provide the `Fintype` structures needed for the preprojective algebra from the corresponding `Finite` instances; the source comments at lines 76–78 describe this setup. Thus the conclusion remains provable after omitting `[Fintype V]`.

### [`ContRepresentation.isUnitary_iff_norm_map`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Continuous/Unitary/Basic.lean#L51-L58) — `tauceti-0058`: flagged only second

- `[NormedAddCommGroup V]`: `InnerProductSpace 𝕜 V` supplies the `SeminormedAddCommGroup V` structure needed for the representation, norms, and `LinearMap.norm_map_iff_inner_map_map`. That lemma is stated with seminormed, not normed, additive groups, so the proof works without this stronger instance. The conclusion and `IsUnitary` remain well-typed, including for zero or trivial spaces.

### [`TauCeti.Multiquadratic.exists_mem_sq_eq_intCast`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/Multiquadratic/Cyclotomic/Embedding.lean#L122-L139) — `tauceti-0071`: flagged only second

- `(hN : 0 < N)`: `hζ : IsPrimitiveRoot ζ N` already forces `N ≠ 0`: if `N = 0`, then `ζ ^ 1 = 1` would imply `0 ∣ 1` by `hζ.dvd_of_pow_eq_one`, a contradiction. Hence `N > 0` follows. Without `hN`, derive this positivity from `hζ` and use it wherever the proof currently passes `hN` (including `exists_mem_sq_eq_natCast` and `hζ.pow`). This also rules out the degenerate case `N = 0`; no extra assumption on `m` is needed.

### [`TauCeti.integrable_norm_sub_sq_of_hasFiniteMoment`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/OptimalTransport/Wasserstein/Basic.lean#L929-L938) — `tauceti-0099`: flagged only second

- `[SecondCountableTopology E]`: The conclusion and its measurability arguments do not require second countability. Without this instance, one can derive the needed L² bounds directly: use `HasFiniteMoment.memLp` with `measurable_edist_right.aestronglyMeasurable` to get `MemLp` of the distance from zero, then `memLp_map_measure_iff` to transfer that bound along each projection, and finally apply `memLp_two_iff_integrable_sq_norm` to the difference. These measurability facts follow from `[OpensMeasurableSpace E]`; the argument works as well for trivial or empty types. The finite-measure assumption remains relevant, since infinite mass at two distinct points can have finite marginal moments while the squared displacement is not integrable.

### [`TauCeti.integralBockstein_modulus_one`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/Bockstein/Integral.lean#L265-L271) — `tauceti-0157`: flagged only second

- `[CompactSpace G]`: For modulus 1, the range criterion gives `1 • y = 0` for every value `y` of the Bockstein, hence `y = 0`. The criterion follows from exactness of the coefficient sequence and does not require compactness; compactness is used for vanishing of integral degree-one cohomology elsewhere, not for this zero-map result. Thus the Bockstein is zero without `[CompactSpace G]`, including degenerate cases.

### [`TauCeti.EisensteinSeries.weightedEisensteinSeries_charWeight_slash`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/ModularForms/EisensteinSeries/Character.lean#L166-L177) — `tauceti-0236`: flagged only second

- `[NeZero N]`: It cannot be deleted: at N = 0, Mathlib defines `ZMod.val` as `Int.natAbs` (Mathlib `Data/ZMod/Basic.lean`, lines 51–59), so `charWeight` loses the sign of its arguments. For example, take u = 3, v = 1, an odd character ψ modulo 3, trivial φ, and γ = -I ∈ Gamma0 0. The weight is even under x ↦ -x, whereas the slash action by -I contributes (-1)^k; for even k the left side is the original series but the claimed scalar is ψ(-1)φ(-1) = -1. Thus the transformation law need not hold at N = 0.

### [`WeierstrassCurve.mem_integralPoints_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/EllipticCurve/Affine/Point/Integral.lean#L71-L76) — `tauceti-0255`: flagged only second

- `[(W.baseChange ℚ).IsElliptic]`: The ellipticity instance is not needed: `integralPoints` is defined directly as the set of points satisfying the displayed existential, and `mem_integralPoints_iff` is `Iff.rfl`. The source also proves the helper lemmas for base change without this instance (`omit [(W.baseChange ℚ).IsElliptic]`). The statement’s point and equation types are meaningful for a non-elliptic curve as well, so dropping the instance leaves the statement unchanged and valid, including in degenerate cases.

## Lean Pool: 13 disagreements

### [`CKN.Leray.integral_ae_eq_integral_jointRep`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegularisedJointRep.lean#L247-L298) — `lean-pool-0024`: flagged first, not again

- `[CompleteSpace E]`: Finite-dimensional normed spaces over a complete field are complete: Mathlib documents `FiniteDimensional.complete` for this purpose. Since ℂ is complete and E is finite-dimensional over ℂ, the proof can obtain `CompleteSpace E` locally from the other assumptions, then proceed unchanged (including the Lp integral). This also covers the zero-dimensional case. Thus the explicit completeness variable can be omitted.

### [`NavierStokes.HeatedOutgoing.E_times_U`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/HeatedOutgoing.lean#L1197-L1206) — `lean-pool-0047`: flagged first, not again

- `(hX : 0 < X)`: The identity also holds for X ≤ 0. In that case X / switchRadius is nonpositive (switchRadius is positive by hXR), so Lean’s Real.log junk-value convention gives log = 0; hence HeatTailEdit.switch is sigma 0 = 0 and the multiplier is 1. Thus heatE equals OutgoingDilation.E there, including X = 0. For X > 0, the existing heatE_times_U proof applies. The patch term still vanishes by correction_times_U_zero, which requires hXR but not hX.

### [`MaxAddDegree.represents_zero_of_degree_lt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConwayRefinement/ConwayRefinement/Algebra/Valuation/DegreeRepresentatives.lean#L140-L143) — `lean-pool-0082`: flagged first, not again

- `[IsOrderedCancelAddMonoid M]`: The statement only needs the degree and additive quotient constructions, which do not require this instance. To prove the class equality without it, unfold `homogeneousMk` using `homogeneousMk_apply`; `componentMk_eq_zero_iff` (which omits this instance) turns `h` into a zero component, and `DirectSum.of` maps zero to zero. The inequality field follows from `h.le`. This also covers the bottom-degree and zero cases, since the argument uses exactly the given strict inequality. The other instances are needed to form `ν : MaxAddDegree R M` or the ordered degree comparison.

### [`NavierStokes.PressureStream.reconstructed_divergence_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PressureStream.lean#L773-L791) — `lean-pool-0120`: flagged first, not again

- `(hab : a < b)`: If `a < b` fails, then the support condition confines `γd` to the empty radial interval when `a > b`, or to the single radial slice `r = a` when `a = b`. In the latter case, continuity from `hγ` and vanishing off that slice force `γd = 0` as well. Thus `weightedSource γd` and hence `streamPotential` are zero, making the divergence conclusion immediate. When `a < b`, the existing proof applies. The binder is not needed to elaborate the statement.

### [`CKN.Core.HeatPotential.heatPotential_series_representation_of_morrey`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Core/HeatPotential/SubordinatedEnd.lean#L24-L142) — `lean-pool-0121`: flagged first, not again

- `(hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)`: The conclusion should hold for any q. For each source, local integrability near q follows by applying `heatPotential_near_kernel_integrable` (or its spatial-kernel counterpart) with center q and radius 1, since q lies in its own closed ball. Away from that neighborhood the kernel is bounded, and compact support together with the Morrey assumptions gives source integrability via `heatPotential_source_integrable_of_compact_support`. Thus the integrands are integrable on the whole domain, allowing the same near/far integral decomposition and summability argument without requiring q to lie near z. The zero/junk cases do not obstruct this argument.

### [`QuantumParallelRepetition.exactReverseAliceMarkedHistoryContext_fiber_iff`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuantumParallelRepetition/Part07.lean#L6721-L6744) — `lean-pool-0155`: flagged first, not again

- `[Fintype X]`: The context and result use X only in function and product types, not in a finite enumeration. The definitions of `exactReverseAliceMarkedHistoryContext` and `finitePrefixMask` need no `Fintype X`; the proof can use the same projection-and-equality argument without this instance.
- `[Fintype Y]`: Y is used as the type of `default` and in function types, but not in a finite enumeration. The context and masking definitions need no `Fintype Y`, so the equality argument remains valid without it.
- `[Fintype A]`: A appears only in outcome and history function types here; the relevant context and history constructions require no `Fintype A`. The proof is based on projections and equality, so this instance can be omitted.
- `[Fintype B]`: B appears only in outcome and history function types here; the relevant context and history constructions require no `Fintype B`. The proof is based on projections and equality, so this instance can be omitted.

### [`TriangleInflation.Peps_tminAI_bounds`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/InflationTermination/TriangleInflation/Exponent.lean#L334-L351) — `lean-pool-0238`: flagged first, not again

- `(h0 : 0 < ε)`: At ε = 0, which is allowed by h1 alone, Real.zero_rpow gives 0 raised to the nonzero exponents in the statement and in Peps. Thus the lower bound's left side is 2. But Peps 0 = Q 0 1 is the deterministic law concentrated on (true, true, true). For every t, the point mass at the all-true assignment witnesses AIFeasible t (Peps 0): its diagonal law is the tensor power of that deterministic law, and its injectable marginals and ancestral products are the corresponding deterministic laws. Hence the rejecting-order set defining tminAI is empty, so by Nat.sInf its value is 0; the lower bound fails. Therefore h0 cannot be deleted.

### [`NRR.Geometry.ConvexBody.neg_carrier`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NandakumarRamanaRao/NRR/Geometry/ConvexBody/SupportFunctionTransform.lean#L107-L108) — `lean-pool-0259`: flagged first, not again

- `[NormedAddCommGroup E]`: This can be omitted: `[InnerProductSpace ℝ E]` supplies the seminormed additive group, topology, and real module structure needed to form `ConvexBody E` and its carrier. The equality is definitional (`rfl`) for every `K`, so the degenerate cases do not require an additional assumption.

### [`AVenhance.Infra.Section4.iterate_corrected_material_unnormalized`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section4/IteratesMaterialBudgetAmplitude.lean#L20-L43) — `lean-pool-0006`: flagged only second

- `(hi : 2 ≤ i)`: The cases i = 0 and i = 1 also satisfy the conclusion, so the proof can split on those cases and use the existing remainder bound for i ≥ 2. By the definitions of iterateAmplitude, the amplitudes at indices 0 and 1 are 1 and C₀ * q, respectively. For i = 0 the inequality reduces, after using C ≥ 0, to 2q² + q ≤ 2/C₀² + 1/C₀; for i = 1 it reduces to q² + q + 1/C₀² ≤ 1/C₀ + 2/C₀². Both follow from 0 < q, 0 < C₀ and C₀ * q ≤ 1. For i ≥ 2 the existing proof applies unchanged.

### [`NavierStokes.ParticularWaveBounds.pressure_class`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ParticularWaveBounds.lean#L1371-L1389) — `lean-pool-0009`: flagged only second

- `(hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)`: A uniform upper bound on N is not needed for the conclusion. The lower bound and hb give ‖N n x‖ ≥ b > 0, so the inverse-square factor is smooth on the domain. Its derivatives are finite sums of products of derivatives of N divided by powers of ‖N‖²; the lower bound controls those denominators, while hN supplies polynomial-growth bounds for the numerator factors. Thus the inverse-square factor, and hence the pressure coefficient and final band-scaled expression, retain the required class bounds without hupper. This also covers the zero case: the lower bound excludes N = 0 wherever the domain is nonempty, and an empty domain makes the pointwise bounds vacuous.

### [`NumberField.Odlyzko.summable_integral_norm_idealSet_complexPlaceMellinGaussian`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/CompletedZeta/ConeGaussianInterchange.lean#L96-L112) — `lean-pool-0115`: flagged only second

- `[IsTotallyComplex K]`: The integral need not be evaluated using the totally-complex formula: integrating each place separately gives a constant times the product of the embedding factors |w(x)|^{-2 s.re}. On the fundamental cone, the normalized embedding coordinates are uniformly comparable, so this product is bounded by a constant times |Norm(x)|^{-α}, where α = 2 s.re (r₁+r₂)/[K:ℚ] ≥ s.re > 1. The resulting series is controlled by `summable_idealSet_inverseNormPower` at exponent α. This also covers fields with real places; ideal-set elements are nonzero, so no zero-value exception arises.

### [`PDL.localInterpolantStep_oneSidedR`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/Local.lean#L307-L366) — `lean-pool-0128`: flagged only second

- `(def_rule : rule = LocalRule.oneSidedR orule YS_def)`: This equality follows from the type of `rule` and the other arguments. In `LocalRule`, the only constructor compatible with source `(∅, Rcond, none)` is `oneSidedR`: `oneSidedL` would require an empty one-sided precondition, ruled out by `OneSidedLocalRule.precond_ne_nil`; the contradiction and loaded constructors have incompatible indices. Matching the result index with `ress_1` and `YS_def` identifies the constructor’s result data, and `OneSidedLocalRule` values with the same precondition are subsingleton (`oneSidedLocalRuleSubsingleton`). Thus `def_rule` can be derived and deleted. These index arguments also cover empty finsets; there is no degenerate constructor exception.

### [`EulerTransversePacketProvider.Forcing.velocityPath_reflection_neg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/TransversePacketParity.lean#L374-L380) — `lean-pool-0247`: flagged only second

- `(hM : ∀ t x, D.M.field t (-x) = D.M.field t x)`: The theorem needs the frame derivative to be even, but this follows from hF without assuming hM: differentiate the equality D.F.field t (-x) = D.F.field t x in time, using D.frame_time to identify the derivatives with D.F₁.field t (-x) and D.F₁.field t x. Applying the coefficient definition then gives evenness of D.frameDerivative. That replaces the use of D.frameDerivative_even hF hM in the proof. The other parity inputs hSym, hraw, and hinit are not supplied by this argument.

## FLT (Anthropic): 33 disagreements

### [`P2MW.S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.Blk176Arith.not_cube_dvd_mul_prod_filter`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.lean#L147-L182) — `flt-anthropic-0038`: flagged first, not again

- `(hN0 : N ≠ 0)`: This follows from `hN3`: if `N = 0`, then `2` is prime and `2 ^ 3 ∣ N` (every natural number divides zero), contradicting `hN3 2 Nat.prime_two`. The proof can first derive `hN0` this way, then use it at the existing factorization steps. Thus the case `N = 0` is already excluded by the remaining hypotheses.

### [`P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.WeierstrassCurve.Affine.isPrincipal_of_geomDivisorSum_eq_zero'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean#L2026-L2070) — `flt-anthropic-0040`: flagged first, not again

- `[DecidableEq F]`: The theorem's statement— including `Divisor.degree` and `geomDivisorSum`—does not require decidable equality on `F`. The proof already begins with `classical`, which supplies the needed decidable equality for its finite-support operations, so the theorem remains provable after deleting this variable hypothesis.

### [`P2MW.S_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq.LanglandsTunnell.CubicInduction.UnipotentEntryHaar.isAddHaarMeasure_map_entry`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq.lean#L119-L129) — `flt-anthropic-0092`: flagged first, not again

- `[BorelSpace (GL (Fin 2) K)]`: The statement's measure and Haar-measure types require the measurable-space instance on `GL (Fin 2) K`, which remains separately available, but they do not require its `BorelSpace` instance. The proof can avoid the `OpensMeasurableSpace` source requirement of `Continuous.isOpenPosMeasure_map`: for an open set in `K`, use `map_apply` with `continuous_entry.measurable` and `BorelSpace K`, then apply `μN`'s open positivity to its open preimage. The compact-finiteness argument via the homeomorphism and left-invariance do not need `BorelSpace (GL (Fin 2) K)` either.

### [`P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift.P2mTwistedShiftDescent.exists_straighten`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift.lean#L314-L368) — `flt-anthropic-0108`: flagged first, not again

- `[SecondCountableTopology G]`: The conclusion and construction need continuity and Borel measurability, but not second countability. The proof's measure-preserving step uses `exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul`, whose hypotheses require a measurable group, sigma-finiteness, and left invariance, but not second countability. The remaining steps use the topological-group structure and continuity of the coordinate formulas. Thus the same construction works without this instance, including for trivial or empty-coordinate cases.

### [`P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual.HopfTransfer.comulAlgHom_eq_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual.lean#L40-L43) — `flt-anthropic-0120`: flagged first, not again

- `[CommRing D]`: The statement and proof only need D to be a semiring with its R-coalgebra structure: `HopfAlgebra R D` supplies those via its `Bialgebra` parent. `Coalgebra.Repr` also needs only the additive/module and coalgebra structures. Thus the theorem and its proof go through without `[CommRing D]`; the remaining `HopfAlgebra R D` supplies the required semiring instance.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal.Ψ₂Sq_𝓦p_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L273-L277) — `flt-anthropic-0125`: flagged first, not again

- `(hp2 : p ≠ 2)`: The excluded case is p = 2. There, the coefficient of X^3 vanishes, but Mathlib defines Ψ₂Sq as 4X^3 + b₂X^2 + 2b₄X + b₆ (DivisionPolynomial.Basic, `Ψ₂Sq`). For 𝓦p 2 over ZMod 2, b₂ = X 0 ^ 2, which is nonzero since MvPolynomial over the field ZMod 2 is a domain and X 0 is nonzero. Thus the coefficient of X^2 is nonzero, so the polynomial is nonzero. A proof can split on p = 2: use that coefficient argument in this case, and retain the existing coefficient-of-X^3 argument for p ≠ 2.

### [`P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.KcSemiLocalIwasawaHaar.mem_K_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean#L1008-L1009) — `flt-anthropic-0126`: flagged first, not again

- `[NumberField L]`: The statement and proof do not require L to be a number field. The source confirms the same semi-local integral-set expressions can be used without this instance: `one_mem_semiLocalIntegralSet` is stated under `omit [NumberField L]`. Here `Iff.rfl` proves the characterization directly from the definitions, without using the number-field structure on L.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.AlgebraicCurve.HolRingFGAux.exists_fin_generators`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.lean#L590-L610) — `flt-anthropic-0132`: flagged first, not again

- `(hN : N.Nonempty)`: If `N` is empty, the condition on `f` says it belongs to every place valuation subring. In a function field of a curve over an algebraically closed field, every nonconstant element has a pole at some place, so such an `f` must lie in `k`. Take `n = 0` and the empty generator map; its generated `k`-algebra is precisely the image of `k`. The nonempty case is the stated theorem.

### [`P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.AlgebraicCurve.BaseChangeTwo.lhs_eq_rhs_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.lean#L327-L359) — `flt-anthropic-0149`: flagged first, not again

- `(hg : g ≠ 0)`: If g = 0, `Place.ord_zero` (in `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`) and hD give D v = 0 for every place v, hence D = 0 by extensionality of `Divisor`. Both lhs and rhs are additive homomorphisms, so they send 0 to 0. Thus the conclusion holds in this case too; the existing proof applies when g ≠ 0.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.P2mFlatIsog.ringKrullDim_stalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.lean#L246-L300) — `flt-anthropic-0150`: flagged first, not again

- `[IsIntegral Y]`: It can be removed: on the chosen nonempty affine open V, put B = Γ(Y,V) and A = Γ(X,h ⁻¹ᵁ V). Since h is finite, B → A is finite; since h is surjective and A is a domain by [IsIntegral X], its kernel is the nilradical of B. Thus B_red embeds integrally into A, and both are finite type algebras over K. Replace the comparison with height_comap_eq for B_red → A; localization at the corresponding primes gives the same stalk dimensions, since quotienting by nilpotents does not change prime spectra or Krull dimensions. This also covers nonreduced Y, including the zero-dimensional case.

### [`P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.NumberTheory.kw_hjoint_normBasis_liftHom_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.lean#L674-L685) — `flt-anthropic-0151`: flagged first, not again

- `[CharZero F]`: The conclusion's types and formula need `[Field F]`, but not characteristic zero: `kw_hjoint_normBasis` is defined by the displayed matrices and polynomial basis identities, and the application proof uses only matrix algebra and `ring`. Those identities remain valid in every characteristic, including characteristic two; no division or cancellation by a nonzero numeral is involved. Thus the `CharZero` instance can be omitted while keeping the statement and proving it by the same calculation.

### [`P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq.DS575Sol.Fbar_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq.lean#L142-L145) — `flt-anthropic-0171`: flagged first, not again

- `[NeZero N]`: The statement's types and quotient are defined without [NeZero N], and the proof uses only Fbar_mk and slashV_add; neither requires it. Gamma_normal, used in defining slashV, also has no nonzero assumption. Thus the same proof works for N = 0 as well as other N, without changing the statement.

### [`P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.HeckeGammaH.sum_slash_beta_eq_heckeU_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean#L381-L463) — `flt-anthropic-0201`: flagged first, not again

- `(B : BezoutData M ℓ)`: `B` appears nowhere in the statement except in its own binder type. It is only used by the proof to choose representatives. From `ρ : Gamma0 M`, the determinant condition and the lower-left divisibility imply that the reduction of the `(1,1)` entry of `ρ` is a unit modulo `M`. By `hρ`, that reduction is `ℓ`, so `¬ ℓ ∣ M`. The source already provides `exists_bezoutData`, which gives a `BezoutData M ℓ` from this fact and the prime hypothesis. Thus, after deleting `B`, the proof can choose such a datum internally and proceed unchanged; the degenerate case `M = 0` is excluded by `[NeZero M]`.

### [`P2MW.S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.lean#L16-L30) — `flt-anthropic-0249`: flagged first, not again

- `[DecidableEq F]`: The statement only uses the field operations, the affine-point group structure, `coordsOrZero`, and the polynomial predicate `IsTwoKernel`; none require decidable equality on `F`. In particular, `coordsOrZero` is defined by point constructors, `IsTwoKernel` is stated using polynomial degree/coefficient/divisibility, and `addOrderOf` is defined without a `DecidableEq` assumption. Removing this binder leaves the statement meaningful, and the proof steps do not use it (the `if_neg` concerns the coefficient index `1`, not `F`).

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.QMHecke12.exists_generator`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.lean#L368-L422) — `flt-anthropic-0252`: flagged first, not again

- `(hι : Function.Injective ι)`: The injectivity assumption can be deleted: `hB` yields `a ≠ 0` and `b ≠ 0`, and `QMPeriodLatticeFull.injective_of_ne_zero` proves that every such algebra homomorphism `ι` is injective. The proof already obtains the required injectivity via `qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span`, without using `hι`.

### [`P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.KcHaarQuotientMulRight.lintegral_density_mul_comp_mul_right_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.lean#L75-L109) — `flt-anthropic-0270`: flagged first, not again

- `[SFinite μH]`: This follows from the other assumptions. The closedness proof gives `SigmaCompactSpace H` via `IsClosed.sigmaCompactSpace`; `[μH.IsHaarMeasure]` provides finiteness on compact sets. Mathlib's `SigmaFinite.of_isFiniteMeasureOnCompacts` then gives `SigmaFinite μH`, which yields `SFinite μH`. Thus the theorem can be proved without taking `[SFinite μH]` as an argument.

### [`P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve.CuspDecayOfAux.qL_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.lean#L116-L119) — `flt-anthropic-0016`: flagged only second

- `[hTΓ : Fact (ModularGroup.T ∈ Γ)]`: The period hypothesis is only used to apply `ModularForm.qExpansion_add` in the given proof. Unfolding `qL`, the equality is additivity of the raw `qExpansion` coefficients: each coefficient is a factorial scalar times an iterated derivative of `cuspFunction`, and iterated derivatives are additive. Thus it holds for any Γ and needs no period assumption; the strict-period condition is not part of the statement's types.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node.B25N3.algebraMap_pow_p`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node.lean#L662-L668) — `flt-anthropic-0027`: flagged only second

- `[Field κ]`: The statement and proof need only a semiring structure on κ, supplied by the remaining `[CharP κ p]` and `[Algebra ℤ_[p] κ]` assumptions. The existing proof's key step can be reproduced without a field: `map_natCast` followed by `CharP.cast_eq_zero κ p` shows the algebra map kills p. The rest uses the reduction of `a ^ p - a` modulo p (`ZMod.pow_card`) and that p maps to zero, so its image is zero. These arguments also cover trivial target rings if the remaining assumptions permit them; no field-specific case is needed.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.CHRAux.Tr_fixed`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_open_eq_comp_aut_of_comp_eq_of_free_of_quotient.lean#L97-L99) — `flt-anthropic-0032`: flagged only second

- `[DecidableEq G]`: The statement and proof need only `[Fintype G]`: `Tr` is defined as a sum over `G`, and `Fintype.sum_equiv` reindexes that sum using an equivalence without requiring decidable equality. Thus the same proof works when `[DecidableEq G]` is omitted, including for groups without a decidable-equality instance.

### [`P2MW.S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.ModularCurve.RiemannHurwitzCount.not_ord_sub_pos_of_ord_sub_pos`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.lean#L307-L323) — `flt-anthropic-0044`: flagged only second

- `(hcc' : c ≠ c')`: If c = c', the premise h is exactly the negation of the conclusion, so the result follows by contradiction. If c ≠ c', the existing proof applies. Thus a proof without hcc' can split on c = c'; no zero or junk-value case causes a problem, since the equality branch uses only h itself.

### [`P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.lean#L843-L876) — `flt-anthropic-0059`: flagged only second

- `(hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)`: The conclusion does not mention ϖ or hϖ. The proof can choose a normalized uniformizer of the completion instead and use it in the intermediate lemmas. Such an element exists because the valuation on this number-field completion has value group ℤ, so an element of valuation −1 has norm (Ideal.absNorm v.asIdeal : ℝ)⁻¹. This does not require any special case for zero or a trivial type: a height-one spectrum point gives a nontrivial discrete valuation.

### [`P2MW.S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.lean#L36-L71) — `flt-anthropic-0083`: flagged only second

- `[NeZero N]`: The statement’s curve types and the proof’s uses of `x1FunctionField N`, `x1FunctionFieldBar N`, and `JOne N` are defined for every natural number N; they do not require N to be nonzero. The proof uses no nonzeroness fact about N, so it works unchanged for N = 0 as well.

### [`P2MW.S_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units.NodeAddEquiv.phi_some`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_Point_exists_addEquiv_nodeNormalForm_additive_units.lean#L81-L82) — `flt-anthropic-0103`: flagged only second

- `[CharZero L]`: The statement uses `Field L` for its operations, but `CharZero L` is not needed to state or prove this definitional equality. After deleting this instance argument, `rfl` still unfolds `phi` and reduces the unit coercion to the displayed fraction; no degenerate case is excluded.
- `[DecidableEq L]`: `DecidableEq L` is not needed by the statement: `Nonsingular` is defined using the curve equation and polynomial nonvanishing, and `Point.some` merely stores such a proof. Although `Point` has a derived `DecidableEq` instance, this statement does not use it. Deleting the instance argument leaves the proof by `rfl` unchanged.

### [`P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.R4GC.qC_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.lean#L1440-L1442) — `flt-anthropic-0104`: flagged only second

- `[NeZero m]`: The statement’s types do not require `m ≠ 0`: `Γ m M'` and `qC` are defined without that instance. The proof uses `ModularForm.qExpansion_eq_zero_iff`, which requires only `one_pos` and `one_mem_strictPeriods`; the latter is proved from `translation_mem_GammaH` and does not require `NeZero m`. Thus the equivalence remains valid, including at `m = 0`, without this hypothesis.

### [`P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.R3M4Torus.ι₀_root`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_measure_fundamentalDomain_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_ellipticCell.lean#L48-L49) — `flt-anthropic-0111`: flagged only second

- `[Fact (Irreducible γ₀.charpoly)]`: The theorem takes this instance because its type mentions γ₀, but neither the type of ι₀ nor AdjoinRoot.root requires irreducibility: ι₀ is defined using the quotient lift and the matrix charpoly identity. The proof `rw [AdjoinRoot.root, ι₀_mk, Polynomial.aeval_X]` also does not use the instance, so it proves the same statement without it.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.M4aD2Skeleton.zetaIntegral_eq_setIntegral_theta'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.lean#L6363-L6392) — `flt-anthropic-0122`: flagged only second

- `(hD'm : MeasurableSet D')`: `hD'` already supplies `NullMeasurableSet D' ν` via the `nullMeasurableSet` field of `IsFundamentalDomain`. The proof uses `hD'm` only for the final set-integral congruence; replacing `setIntegral_congr_fun hD'm` with `setIntegral_congr_fun₀ hD'.nullMeasurableSet` proves the same pointwise congruence. This also covers degenerate sets such as the empty set.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.R4TateModelKHb.Xc_def`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_variableChange_weightOne_tateBase_one_mem_laurentBaseChange_and_tateToricPoint_mem_of_ker.lean#L362-L362) — `flt-anthropic-0230`: flagged only second

- `[CharZero L]`: The statement mentions L, so the instance-implicit variable [CharZero L] is included as an argument. It is not needed: the equality is definitional (`rfl`), and the statement’s operations are supported by [Field L] alone. Removing [CharZero L] leaves the statement elaborable and the same proof works.

### [`P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.EtaleCoordK1a.rankAtStalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean#L13-L24) — `flt-anthropic-0236`: flagged only second

- `[Module.FinitePresentation S M]`: This is used only to apply the locally-constant-rank lemma in the given proof. For any prime p, the same localization-rank argument used at ⊥ works directly: since S is a domain, p.asIdeal.primeCompl consists of nonzero elements and is contained in nonZeroDivisors S. Apply IsLocalization.rank_eq and IsLocalizedModule.rank_eq to get rank of the localized module equal to hrank, then Module.finrank_eq_of_rank_eq gives the stated equality. The latter lemma requires only the rank equality, not finite presentation.
- `[Module.Flat S M]`: Flatness is used only for the locally-constant-rank step in the given proof. As above, for each p the localization-rank equalities directly identify the stalk's rank with Module.rank S M; this proof works without flatness, including at every prime of the domain.

### [`P2MW.S_ModularCurve_NodeLocalized_exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint.PowerSeries.Submodule.COMP.θ_X_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_NodeLocalized_exists_surjective_mvPowerSeries_adicCompletion_modularLocalizedAtPoint.lean#L806-L808) — `flt-anthropic-0237`: flagged only second

- `[Fact (Irreducible ϖ)]`: The theorem only uses ϖ to form the quotient W ϖ and the maps θ₀, θW, θ₁, and θ₂; their definitions and the X-zero computation do not require ϖ to be irreducible. The quotient by the ideal generated by X − C ϖ and the displayed ring-map identities are defined for any ϖ, so the same proof works after omitting this instance.

### [`WeierstrassCurve.zero_mem_kernelIdealSet`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_WeierstrassCurve_KernelIdeal.lean#L16-L19) — `flt-anthropic-0246`: flagged only second

- `[DecidableEq k]`: The statement does not require decidable equality on `k`: `IsRationallyRepresented` and `rationalHomSet` are defined without using it, and `rationalEndSubring` and `kernelIdealSet` only build on those definitions. The witness remains `0`, using `zero_mem_rationalHomSet`; the zero-composition equality is unchanged. This argument also works for empty or trivial types, since it uses no elements of `k` or equality decisions on them.

### [`P2MW.S_RubinSilverberg_exists_polynomial_rsFamily.M4cP2.D52.PhiA_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_RubinSilverberg_exists_polynomial_rsFamily.lean#L410-L414) — `flt-anthropic-0247`: flagged only second

- `(hj : j < 21)`: The two sides, viewed as polynomials in the parameter `t`, have degree at most 20: `lhsPairAG` uses fifth powers of linear expressions in `t`, and the `hornerG` term is built from the 21-entry `tabA` list. For each fixed `s < 197`, `gridA` gives equality at `t = 0, …, 20`; the degree bound and the same finite-evaluation root argument used in this theorem then give equality for every `t`, including `j ≥ 21`. Applying the existing 197-point evaluation argument in `X` proves the stated polynomial equality without `hj`. This works over `ℤ` without an excluded zero or other degenerate case.

### [`P2MW.S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.CerednikDrinfeld.BrandtLevel.mem_modOf_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_exists_units_image_kernelIdealSet_pair_eq_image_mul_of_comp_eq_id_forall_mem_ker.lean#L566-L575) — `flt-anthropic-0272`: flagged only second

- `[IsAlgClosed κ]`: The statement and proof do not need algebraic closedness: the rationalHomSet definition uses Field and DecidableEq, and the proof is just the map-membership equivalence for modOf followed by unpacking the subgroup subtype. The same proof works over any field κ with the other assumptions; there is no exceptional empty or trivial case.

### [`P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.lean#L110-L138) — `flt-anthropic-0294`: flagged only second

- `[IsDomain A]`: This instance follows from the other assumptions: `IsFractionRing.isDomain_iff_isField` gives `IsDomain A ↔ IsField K`, and `[Field K]` supplies the right-hand side. After deleting the binder, the proof can locally install the resulting `IsDomain A` instance and proceed unchanged. The field assumption rules out the degenerate zero-ring case.

## Formal Frontier: 8 disagreements

### [`CategoryTheory.splitKernelProductIso_mul_lift`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupObject/SplitKernelSemidirect.lean#L115-L126) — `formal-frontier-0072`: flagged first, not again

- `[IsMonHom i]`: The statement and proof need i only as a morphism: splitKernelConj and splitKernelProductIso do not require i to preserve multiplication. The group calculation can be proved using splitKernelConj_lift_comp_i, whose statement and proof require neither [IsMonHom i] nor [IsMonHom e], followed by the group laws. The argument remains valid in degenerate cases since it uses only the stated group-object laws and pullback property.
- `[IsMonHom e]`: The product isomorphism and restricted conjugation are defined for an arbitrary section e satisfying he; neither requires e to preserve multiplication. The proof's conjugation readback splitKernelConj_lift_comp_i holds without [IsMonHom e], so the remaining equality follows from group laws on the morphisms. No degenerate case requires multiplicativity of e.

### [`FundamentalGroup.existsUnique_hom_of_isOpenCover`](https://github.com/FormalFrontier/fundamental-groupoids/blob/2fdb99858e3feb7a6a06ae10915f286364de2cc1/FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean#L404-L527) — `formal-frontier-0164`: flagged first, not again

- `(hU : IsPathConnected (U : Set X))`: This can be deleted on its own: only the path component of p in U matters to the based fundamental group. Since hI makes the entire overlap path connected and it contains p, every component of U that meets V is the component of p; any other U-components are disjoint from V and do not affect based loops in X. The descent proof can therefore use paths and frames on the components relevant to p, without requiring all of U to be path connected. The point p still supplies a nonempty relevant component.
- `(hV : IsPathConnected (V : Set X))`: Symmetrically, this can be deleted on its own: every component of V meeting U is the component of p, by path connectedness of the overlap, and components disjoint from U do not affect based loops in X. Restricting the descent argument to the components relevant to p gives the same extension and uniqueness. The point p ensures the relevant component is nonempty.

### [`DirectLimit.VaryingScalar.fromTensorLimit_mk`](https://github.com/FormalFrontier/algebraic-direct-limits/blob/1bf0740b01951905e0ba12bd5d2bdb67819c12d1/AlgebraicDirectLimits/VaryingScalar.lean#L389-L392) — `formal-frontier-0210`: flagged first, not again

- `[Nonempty ι]`: The theorem’s statement and its `rfl` proof do not need a chosen index: the direct-limit types and maps in the statement are well-typed without `[Nonempty ι]`. Removing this instance leaves the theorem universally quantified over `i : ι`; if `ι` is empty, there is no such `i`, so the claim is vacuous. The other order assumptions and algebraic instances remain available.

### [`CountableEndomorphism.free_kernel`](https://github.com/FormalFrontier/stable-range/blob/c283b01ed9ebc33c7eefcdb4f3d2ca45141f469e/StableRange/CountableEndomorphism.lean#L251-L262) — `formal-frontier-0257`: flagged first, not again

- `[AddCommGroup M]`: The statement still makes sense for an `AddCommMonoid` module: the Finsupp parity splitting and the endomorphism semiring do not require additive inverses. The kernel is directly isomorphic, as a module over the opposite endomorphism semiring, to one copy of `Module.End S (ℕ →₀ M)`: send a kernel element `k` to `y₁ * k`, with inverse `r ↦ x₁ * r`. The parity decomposition identity `x₀ * y₀ + x₁ * y₁ = 1` shows these maps are inverse on the kernel, since `y₀ * k = 0`. The endomorphism semiring is free over itself, so freeness follows without the group hypothesis; this direct argument replaces the current proof’s ring-based rectangular-inverse criterion. The trivial-module case is included: both the kernel and coefficient semiring are trivial.

### [`ProjectiveSpace.finrank_homogeneousSubmodule_fin`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/HomogeneousDimension.lean#L58-L65) — `formal-frontier-0115`: flagged only second

- `[StrongRankCondition R]`: The statement itself only needs `[CommSemiring R]`. The same proof works without the strong rank condition: the homogeneous-component equivalence to a supported Finsupp module and `Module.finrank_finsupp_self` require no such condition; the latter follows from the general `CommSemiring.rank_self`. The remaining cardinality and arithmetic steps are independent of `R`. This also covers degenerate rings, including the zero semiring, since the cited rank result holds for commutative semirings generally.

### [`AlgebraicGeometry.matrixStdBasis_dual_apply`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/MatrixEndAdditive.lean#L70-L77) — `formal-frontier-0140`: flagged only second

- `[DecidableEq (m × n)]`: `Matrix.stdBasis` only requires `[Fintype m]`, `[Finite n]`, and `[Semiring K]`; its `dualBasis` is available because `m × n` is finite. Neither `Module.Basis.dualBasis_apply` nor `matrixStdBasis_repr` requires decidable equality. Thus the identity remains provable without this instance.

### [`AlgebraicGeometry.isIntegrallyClosed_stalk_of_specializes`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/Normal.lean#L279-L308) — `formal-frontier-0174`: flagged only second

- `[_root_.IsDomain (X.presheaf.stalk y)]`: A scheme stalk is a local ring, and an integrally closed local ring is a domain. Thus the remaining hypothesis `[_root_.IsIntegrallyClosed (X.presheaf.stalk y)]` supplies this domain property, so the explicit domain assumption can be removed; the localization argument then applies unchanged. The stalk at a scheme point is nontrivial, so there is no zero-ring exception.

### [`MonomialOrder.restrictedResidue_support_eq_of_unit_factor`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/LeadingTerm.lean#L502-L543) — `formal-frontier-0258`: flagged only second

- `[ValuationRing R]`: The statement and proof use only commutative-ring operations, ideal quotients, and the adically restricted subring, whose definition requires only `[CommRing R]`. The coefficientwise proof works without valuation-ring properties. Keeping `[IsDomain R]` while deleting this instance still lets the statement elaborate; the degenerate cases are covered by the same coefficientwise argument.

