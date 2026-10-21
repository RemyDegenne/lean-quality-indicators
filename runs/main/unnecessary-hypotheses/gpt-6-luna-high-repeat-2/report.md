# unnecessary-hypotheses: run `main`, judge `gpt-6-luna-high-repeat-2`

| Library | Sampled | Judged | Flagged | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|
| Mathlib | 1000 | 300 | 11 | 3.7% | 2.1%–6.4% | unknown |
| Tau Ceti | 1000 | 300 | 18 | 6.0% | 3.8%–9.3% | unknown |
| Lean Pool | 1000 | 300 | 51 | 17.0% | 13.2%–21.7% | unknown |
| FLT (Anthropic) | 1000 | 300 | 60 | 20.0% | 15.9%–24.9% | unknown |
| Formal Frontier | 1000 | 300 | 15 | 5.0% | 3.1%–8.1% | unknown |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (11 flagged)

### [`RatFunc.Luroth.Φ_natDegree_eq_φ_natDegree`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/RatFunc/Luroth.lean#L182-L185) — `mathlib-0077`

Snippet: `samples/mathlib/mathlib-0077.lean`

- `(h : E ≠ ⊥)` (theorem): When E = ⊥, X is transcendental over E (the bottom intermediate field is K, and `transcendental_X` applies), so `minpoly` is 0 by the definition in `Minpoly/Basic.lean`; hence `(φ E).natDegree = 0`. Its mapped polynomial is also 0, so `integerNormalization` is 0 by `integerNormalization_eq_zero_iff` in `RingTheory/Localization/Integral.lean`. Since `primPart_zero` in `RingTheory/Polynomial/Content.lean` gives `0.primPart = 1`, `(Φ E).natDegree = 0` too. Thus the equality holds in the omitted case; retain the existing proof when E ≠ ⊥ and handle E = ⊥ by these simplifications.

### [`Module.Basis.toMatrix_mulVec_repr`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Matrix/Basis.lean#L231-L236) — `mathlib-0083`

Snippet: `samples/mathlib/mathlib-0083.lean`

- `[Finite ι']` (theorem): The statement only needs `[Fintype ι]` for the matrix-vector product; it does not require the row index type `ι'` to be finite. Without `[Finite ι']`, prove the equality by extensionality on `ι'`, expand `mulVec` and `Basis.toMatrix`, and use the finite basis expansion `b.sum_repr m` followed by the linear map `b'.repr` to identify each coordinate. This argument works for arbitrary `ι'` and does not rely on a nonempty or nontrivial index type.

### [`Unitization.cobounded_eq_aux`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Algebra/Unitization.lean#L195-L198) — `mathlib-0113`

Snippet: `samples/mathlib/mathlib-0113.lean`

- `[NormedSpace 𝕜 A]` (variable): The bornology equality is independent of the scalar normed-space structure. The `Unitization` bornology is induced by `addEquiv`; its definition and the conclusion use only the additive structures already supplied by the other assumptions. The equality can be proved by reflexivity, including in degenerate cases.
- `[IsScalarTower 𝕜 A A]` (variable): The bornology equality is independent of the scalar tower structure. The `Unitization` bornology is induced by `addEquiv`, so the conclusion can be proved by reflexivity without this assumption.
- `[SMulCommClass 𝕜 A A]` (variable): The bornology equality is independent of this scalar-action commutation property. The `Unitization` bornology is induced by `addEquiv`, so the conclusion can be proved by reflexivity without it.
- `[RegularNormedAlgebra 𝕜 A]` (variable): Although this assumption is used by the Lipschitz proof in the file, the bornology equality itself is just the equality between `cobounded` for the induced bornology and for `Unitization`'s bornology, which is defined as `Bornology.induced (addEquiv 𝕜 A)`. The conclusion can therefore be proved by reflexivity without the regularity assumption, even in degenerate cases.

### [`MeasureTheory.projectiveFamilyContent_mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean#L134-L137) — `mathlib-0116`

Snippet: `samples/mathlib/mathlib-0116.lean`

- `(hs : s ∈ measurableCylinders α)` (theorem): If `hs` fails, `projectiveFamilyContent_eq` and the definition of `projectiveFamilyFun` show `projectiveFamilyContent hP s = 0`, so the inequality follows from nonnegativity of `projectiveFamilyContent hP t`. If `hs` holds, `addContent_mono` proves the result using `ht` and `hst`. Thus `hs` can be deleted without changing the conclusion.

### [`WeierstrassCurve.preΨ_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean#L314-L318) — `mathlib-0123`

Snippet: `samples/mathlib/mathlib-0123.lean`

- `[Nontrivial R]` (theorem): The hypothesis h already implies Nontrivial R: use `nontrivial_of_ne (n : R) 0 h`. Thus, without the instance binder, a proof can install this as a local instance and use the existing proof, including `W.preΨ'_ne_zero`. In a trivial ring h cannot hold, so there is no degenerate countercase.

### [`AdicCompletion.tensor_map_id_left_injective_of_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean#L367-L373) — `mathlib-0139`

Snippet: `samples/mathlib/mathlib-0139.lean`

- `[Module.Finite R M]` (variable): This follows from the other assumptions and `hf`: `IsNoetherianRing R` and `[Module.Finite R N]` give `IsNoetherian R N`, so `Module.Finite.of_injective f hf` supplies `[Module.Finite R M]`. Thus the proof can obtain this instance locally and proceed unchanged. This also covers degenerate cases, since injectivity into a trivial or zero module forces the source to be trivial.

### [`continuous_parametric_integral_of_continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/Bochner/Set.lean#L1121-L1139) — `mathlib-0190`

Snippet: `samples/mathlib/mathlib-0190.lean`

- `[FirstCountableTopology X]` (theorem): This is only needed by the dominated-convergence proof. Without it, compactness of `s` and continuity of `f.uncurry` give, for every `x₀` and ε>0, a neighborhood of `x₀` on which `‖f x y - f x₀ y‖ < ε` for every `y ∈ s`: take product neighborhoods from continuity at each `(x₀,y)` and a finite subcover of `s`. Since `s` has finite measure, the integral difference is then bounded by `ε * μ s`, proving continuity directly. This argument works for arbitrary `X`; the other assumptions still provide the needed measurability and finite measure.

### [`HomologicalComplex.pOpcycles_extendOpcyclesIso_inv`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Homology/Embedding/ExtendHomology.lean#L372-L383) — `mathlib-0257`

Snippet: `samples/mathlib/mathlib-0257.lean`

- `[(K.extend e).HasHomology j']` (variable): The extension homology instance is derivable from `[K.HasHomology j]` and `hj'`: `extend` has an instance at `e.f j` from `[K.HasHomology j]` (line 285 of `ExtendHomology.lean`), and `hj'` identifies `e.f j` with `j'`. Thus this variable can be omitted while the statement's required instance is synthesized.

### [`ProbabilityTheory.Kernel.withDensity_rnDeriv_of_subset_compl_mutuallySingularSetSlice`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Kernel/RadonNikodym.lean#L336-L367) — `mathlib-0258`

Snippet: `samples/mathlib/mathlib-0258.lean`

- `(hsm : MeasurableSet s)` (theorem): The measures agree after restricting to the measurable set `(mutuallySingularSetSlice κ η a)ᶜ`: for any measurable test set, apply this theorem to its intersection with that complement, which is measurable. Equality of the restricted measures then gives equality on arbitrary `s` contained in the complement, since evaluating a restricted measure on `s` does not require `s` itself to be measurable. Thus `hsm` can be removed; the finite-kernel assumptions remain available for establishing the restricted-measure equality.

### [`add_tsub_add_le_tsub_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Sub/Defs.lean#L160-L162) — `mathlib-0260`

Snippet: `samples/mathlib/mathlib-0260.lean`

- `[AddLeftMono α]` (variable): OrderedSub already implies addition is monotone. For fixed b, `tsub_le_iff_right` gives `(a - b ≤ c) ↔ (a ≤ c + b)`. If c ≤ d, first use the equivalence to get `(c + b) - b ≤ c`, then transitivity gives `(c + b) - b ≤ d`, and the equivalence yields `c + b ≤ d + b`. Thus addition is monotone on the right; commutativity gives monotonicity on the left. This supplies the needed `AddLeftMono α` locally, so the theorem can be proved without taking it as an argument.

### [`MeasureTheory.Measure.prod_smul_left`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Prod.lean#L877-L881) — `mathlib-0275`

Snippet: `samples/mathlib/mathlib-0275.lean`

- `[hν : SFinite ν]` (variable): This instance can be deleted: by the definition of `Measure.prod` (Prod.lean, lines 169–177), if `ν` is not S-finite then both products in the equality are zero, so the equality still holds. If `ν` is S-finite, the existing proof using `prod_apply` applies. Thus a case split on `SFinite ν` proves the result without the instance, including the non-S-finite case.


## Tau Ceti (18 flagged)

### [`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/Basic.lean#L952-L963) — `tauceti-0001`

Snippet: `samples/tauceti/tauceti-0001.lean`

- `(hN : N ≠ 0)` (theorem): At N = 0, `Nat.primeFactors 0` is empty, so the right-hand side is 0 and the prime-factor product on the left is 1. Also `(Gamma0 0).index = 0`: `Gamma0 0` consists of matrices with lower-left entry zero, and the matrices with rows `(1, 0)` and `(n, 1)` give infinitely many distinct cosets (their pairwise differences have lower-left entry `n - m`). By `Subgroup.index_eq_zero_iff_infinite`, the index is zero. Thus the equality holds at zero as well; the existing proof can handle this case separately and use the given proof for nonzero N.

### [`TauCeti.ContCohomology.homogeneous2_coe_apply_one`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/Shapiro/Basic.lean#L460-L466) — `tauceti-0005`

Snippet: `samples/tauceti/tauceti-0005.lean`

- `[IsTopologicalGroup G]` (variable): The statement and proof are algebraic: `homogeneous2` is defined using only the group operations and the action, and `DiscreteCoind` is defined with `[Group G]` and `[TopologicalSpace G]`, not `[IsTopologicalGroup G]`. Removing this instance leaves the statement elaborable, and the `simp` proof is unchanged; no degenerate case is excluded.

### [`RootPairing.coroot'_nonpos_of_mem_negRoots`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/Chamber.lean#L325-L331) — `tauceti-0007`

Snippet: `samples/tauceti/tauceti-0007.lean`

- `[IsDomain R]` (variable): The nonnegative-coroot expansion used in the proof needs no domain assumption: expand the positive root for `P.flip` using `exists_root_eq_sum_nat_of_mem_posRoots`, use `posRoots_flip`, and transport the equality through the coroot linear map. The resulting sum has natural-number coefficients, so `Finset.sum_nonneg` and `nsmul_nonneg` prove nonnegativity. The domain assumption is only used by `exists_coroot'_eq_sum_nat_of_mem_posRoots` to additionally show that some coefficient is nonzero; that fact is unnecessary here. Reflecting the negative root and negating the inequality then gives the stated result. This argument also covers the case where every coefficient is zero.

### [`TauCeti.cohomologicalDimensionAt_eq_of_isOpen_of_ne_top`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/CohomologicalDimension/OpenSubgroup.lean#L108-L115) — `tauceti-0009`

Snippet: `samples/tauceti/tauceti-0009.lean`

- `[TotallyDisconnectedSpace G]` (variable): This can be deleted: for a compact topological group, an open subgroup has finite index, and the finite-index coinduction/trace argument gives the reverse inequality when `cohomologicalDimensionAt p G ≠ ⊤`; the closed-subgroup inequality gives the other direction. The argument does not require total disconnectedness. The other hypotheses are needed: without compactness, for example, `ℤ` with its discrete topology and its open trivial subgroup have dimensions 1 and 0; without `hU`, a closed trivial subgroup of `ℤ_p` gives dimensions 0 and 1; and the finite-dimension assumption is essential as the file’s `ℤ/p` example indicates.

### [`HeckeRing.GLn.posDetInt_le_commensurator`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/HeckeRing/GLn/Basic.lean#L712-L717) — `tauceti-0020`

Snippet: `samples/tauceti/tauceti-0020.lean`

- `[NeZero n]` (variable): The inclusion also holds for n = 0: matrices indexed by Fin 0 are unique, so GL (Fin 0) ℚ is subsingleton and its subgroups are commensurable, making the commensurator all of GL (Fin 0) ℚ. For n ≠ 0, the existing proof applies after supplying NeZero n from n ≠ 0; the argument uses only integrality, not positivity.

### [`TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Data/Nat/Factorization/GcdSplit.lean#L56-L71) — `tauceti-0078`

Snippet: `samples/tauceti/tauceti-0078.lean`

- `(hp : p.Prime)` (theorem): The identity also holds when `p` is not prime: Mathlib gives `ordCompl[p] n = n` (`Nat.ordCompl_of_not_prime`) and `n.factorization p = 0` (`Nat.factorization_eq_zero_of_not_prime`), so the right side simplifies to `Nat.gcd m n`. A proof can split on `p.Prime`, use the existing proof in the prime case, and simplify in the other case. The nonzero hypotheses remain necessary: if, for example, `m = 0`, `p = 2`, and `n = 2`, the two sides are `2` and `1`. ⊥

### [`TauCeti.exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Cohomology.lean#L195-L206) — `tauceti-0118`

Snippet: `samples/tauceti/tauceti-0118.lean`

- `[IsNonarchimedeanLocalField K]` (variable): The statement and the proof via `groupCohomology_res_padicCompletionUnits` do not use this local-field assumption on K. The representation and cohomology expression only require the other hypotheses; this is also reflected in the source theorem’s variable context, which does not include local-field assumptions on K. The neighboring `[ValuativeRel K]` and `[TopologicalSpace K]` must remain to elaborate the remaining local-field-related binder types, but this binder itself can be omitted.
- `[CharZero K]` (variable): This is implied by `[Field K]` and `[Algebra ℚ_[p] K]`: the algebra map from the characteristic-zero field ℚ_[p] into the field K is injective, so `charZero_of_injective_algebraMap` supplies `CharZero K`. The proof and statement can use that derived instance instead.
- `[CharZero L]` (variable): This is implied by `[Field L]` and `[Algebra ℚ_[p] L]` in the same way: the algebra map from ℚ_[p] into L is injective, and `charZero_of_injective_algebraMap` supplies `CharZero L`. The proof can use the derived instance instead.

### [`Matrix.ProjectiveSpecialLinearGroup.isParabolic_inv_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup/FinTwo.lean#L103-L117) — `tauceti-0134`

Snippet: `samples/tauceti/tauceti-0134.lean`

- `[NoZeroDivisors R]` (variable): The definition of `IsParabolic` on `PSL(2, R)` is existential: it requires a parabolic `SL(2, R)` representative. For any representative, inversion uses its inverse, which is represented by its adjugate. In dimension two, the adjugate has the same trace and determinant, and is scalar exactly when the original matrix is scalar; these facts do not require `NoZeroDivisors R`. Thus the existential witnesses transfer in both directions. The assumption is needed by `isParabolic_mk_iff` to compare all representatives, but that lemma can be avoided here. This also covers the zero ring, where both sides are false.

### [`TauCeti.Manifold.christoffelMap_coordChange`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Geometry/Manifold/VectorBundle/CovariantDerivative/Coordinate/Change.lean#L52-L207) — `tauceti-0155`

Snippet: `samples/tauceti/tauceti-0155.lean`

- `[CompleteSpace 𝕜]` (variable): The statement and the coordinate-change/manifold and covariant-derivative results used in the proof do not require completeness; the relevant tangent-coordinate-change regularity theorem has no `CompleteSpace` assumption. The proof can use the same argument without this instance, including over an incomplete nontrivially normed field.
- `[FiniteDimensional 𝕜 E]` (variable): With `[Fintype ι]` and the basis `b`, finite dimensionality follows from `b.finiteDimensional_of_finite`. The statement's `christoffelMap` is defined for a fintype-indexed basis without a finite-dimensionality assumption, so after deleting this variable the proof can locally install that derived instance and proceed unchanged.

### [`TauCeti.rightTrace_biprod`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/CategoryTheory/Monoidal/Pivotal/Biproduct.lean#L114-L125) — `tauceti-0163`

Snippet: `samples/tauceti/tauceti-0163.lean`

- `[MonoidalPreadditive C]` (variable): This instance is used by the displayed proof for additivity of whiskering and `rightTrace_add`, but it can be removed for this theorem. Since `C` is rigid, tensoring by a fixed object has adjoints and preserves any biproduct that exists. In particular, the needed whiskering preserves the given binary biproduct; the biproduct decomposition and cyclicity of `rightTrace` then prove the stated diagonal formula without assuming global additivity of tensoring. The other assumptions still provide the category, trace, preadditive hom addition, and biproduct notation required by the statement.

### [`TauCeti.FiniteTypeCommHopfAlgCat.range_identityComponentPointsHom`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/AlgebraicGroup/Connected/GroupScheme.lean#L242-L250) — `tauceti-0173`

Snippet: `samples/tauceti/tauceti-0173.lean`

- `[IsAlgClosed k]` (variable): The statement’s types and the definitional equality proved by `rfl` do not depend on algebraic closedness. The identity-component point map is defined as `quotientPointsHom`, and its range reduces definitionally to `quotientPointsSubgroup`; the same `rfl` proof works without this instance. The `Field k` assumption remains available for the other types in the statement.

### [`TauCeti.ContCohomology.indexTwoShortExact_explicitDelta0`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Homological/ContCohomology/Coinduced/IndexTwo.lean#L177-L186) — `tauceti-0185`

Snippet: `samples/tauceti/tauceti-0185.lean`

- `[CompactSpace G]` (variable): This instance can be omitted while leaving the statement and proof unchanged. The cohomology carriers H0 and H1 and the short-exact-sequence construction do not require compactness of G; the displayed proof uses the representative and connecting-map lemmas without it. No compactness-dependent step or degenerate case is involved.

### [`TauCeti.exists_coprimePart_indK0_of_trivial_eq_nsmul`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Permutation/PrimePower.lean#L131-L148) — `tauceti-0194`

Snippet: `samples/tauceti/tauceti-0194.lean`

- `[Fact p.Prime]` (variable): With `[Field k]` and `[CharP k p]`, `CharP.char_is_prime_or_zero` gives either `p.Prime` or `p = 0`. In the prime case, the existing proof applies by supplying the resulting `Fact p.Prime`. In the zero case, choose `D = C`: `Nat.factorization_zero_right` makes the scalar `0 ^ 0 = 1`, `D.relIndex C = 1`, and `¬ 0 ∣ Nat.card C` since `C` is finite and has positive cardinality. The `indK0` equality is then the identity `1 • x = x`. Thus the theorem remains true without this instance.

### [`TauCeti.IsGradedExtInternallyFinite.shiftSourceInverse`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Homology/EulerCharacteristic/ExtEuler/Graded/Shift.lean#L304-L308) — `tauceti-0229`

Snippet: `samples/tauceti/tauceti-0229.lean`

- `[e.functor.Additive]` (variable): An equivalence between abelian categories preserves finite biproducts, and addition of morphisms is determined by the biproduct diagonal and codiagonal. Thus `e.functor` is additive even without this instance; locally supplying that instance lets the existing proof use `gradedExtShiftSourceInverse`. This also holds in degenerate or zero categories.

### [`TauCeti.cwEulerChar_preimage_of_card_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/Covering.lean#L75-L88) — `tauceti-0231`

Snippet: `samples/tauceti/tauceti-0231.lean`

- `(hfin : ∀ b, Finite ↥(p ⁻¹' {b}))` (variable): The cell-count proof can use `Nat.card_congr (cellPreimageEquiv C hp n)`, `Nat.card_sigma`, and `finsum_eq_sum_of_fintype` without assuming the fibers are finite. If a fiber is infinite, `Nat.card` is 0; the hypothesis `hd` then forces `d = 0` on fibers over `C`, and the same cell-count and finite-range Euler-characteristic argument still gives the result. The finite-fiber assumption is used by the existing helper lemma, but is not needed for this argument.

### [`TauCeti.mem_integralWeightLattice_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/WeightLattice.lean#L194-L199) — `tauceti-0234`

Snippet: `samples/tauceti/tauceti-0234.lean`

- `[FiniteDimensional K L]` (variable): The statement and proof do not require finite dimensionality: `integralWeightLattice` has carrier `IsIntegralWeight`, whose definition quantifies over `Weight K H L` and uses `IsKilling.coroot`, with no `[FiniteDimensional K L]` requirement. Thus `Iff.rfl` still proves the equivalence after omitting this variable.

### [`TauCeti.schwarzChristoffelEdgeAngle_comp_strictMono`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/GlobalTurning.lean#L114-L125) — `tauceti-0238`

Snippet: `samples/tauceti/tauceti-0238.lean`

- `[LocallyFiniteOrder ι]` (variable): The conclusion does not require locally finite intervals; this instance is only used by the proof’s helper involving `Finset.Ioc`. A proof without it can use `schwarzChristoffelEdgeAngle_sub`, which expresses the angle difference as a sum over a filtered `Finset.univ` and requires no locally finite order. Strict monotonicity of `a` makes that filter nonempty (it contains `j`) and every summand is negative by `he`, so the angle difference is positive. This also covers an empty index type, where strict monotonicity is vacuous.

### [`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isCompact`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/PDE/Regularity/HolderContinuity.lean#L238-L258) — `tauceti-0281`

Snippet: `samples/tauceti/tauceti-0281.lean`

- `[Nonempty ι]` (theorem): If ι is nonempty, the existing proof applies. Otherwise the finite type ι is empty, and `EuclideanSpace ℝ ι` is a singleton since it is `PiLp 2` of functions indexed by ι (Mathlib `PiL2.lean`, lines 108–115). Thus any two points of K coincide, so the precise representative is Hölder on K, for example with α = 1 and C = 0; this remains true in the empty-K case. The proof without this hypothesis can split on whether ι is empty and use `HolderOnWith.of_dist_le` for the singleton case.


## Lean Pool (51 flagged)

### [`ViscositySolns.exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Aleksandrov/JetCalculus/Strictification/StrictifiedObjective.lean#L337-L370) — `lean-pool-0000`

Snippet: `samples/lean-pool/lean-pool-0000.lean`

- `(hr : 0 <= r)` (theorem): If `r < 0`, `Metric.closedBall (0 : Point n) r` is empty because distances are nonnegative, so `CoordinateSemiconvexOn` holds vacuously (for example with `lambda = 0`). If `0 <= r`, the existing proof via `coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall_of_entrywise_abs_le` applies. Thus the result holds without `hr`. The empty-ball case also covers `n = 0`; no nonemptiness assumption is needed.

### [`Bananas.marks_ne_of_allSubmodular_banana`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BrillNoetherGraphs/Bananas/Theta/ThetaBoundarySubmodularity.lean#L847-L855) — `lean-pool-0015`

Snippet: `samples/lean-pool/lean-pool-0015.lean`

- `(hg : 1 ≤ g)` (theorem): This is needed to exclude genus zero. For example, a banana with g = 0 and its single strand of length 1 is a connected genus-zero graph. By `rank_eq_degree_or_neg_one_of_connected_genus_zero`, rank is f(n) = -1 for n < 0 and f(n) = n otherwise, where n is divisor degree. With u = v, `rankDelta` depends only on degree and is f(n) - 2f(n - 1) + f(n - 2), which is 0 for every integer n. Thus the marking is all-submodular even though u = v, so deleting hg makes the theorem false.

### [`CKN.Leray.integral_ae_eq_integral_jointRep`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegularisedJointRep.lean#L247-L298) — `lean-pool-0024`

Snippet: `samples/lean-pool/lean-pool-0024.lean`

- `[CompleteSpace E]` (variable): Finite-dimensional normed spaces over a complete field are complete: Mathlib documents `FiniteDimensional.complete` for this purpose. Since ℂ is complete and E is finite-dimensional over ℂ, the proof can obtain `CompleteSpace E` locally from the other assumptions, then proceed unchanged (including the Lp integral). This also covers the zero-dimensional case. Thus the explicit completeness variable can be omitted.

### [`IsoGraph.Canon.splitCell_tr_general`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Equivariance.lean#L3331-L3342) — `lean-pool-0028`

Snippet: `samples/lean-pool/lean-pool-0028.lean`

- `(hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))` (theorem): The conclusion concerns only the trace. After unfolding `splitCell` and using `h1`, `hb`, `h2`, and `ho`, the trace comes from the `boundsFrom` match; its result is independent of the values returned by `scatterFrom`. A proof without `hsc` can destructure that match directly and then use `hbd`.
- `(hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))` (theorem): The conclusion concerns only the trace, which is independent of the `lab` and `pos` returned by `writeFrom`. A proof without `hw` can destructure the `writeFrom` match directly and then use `hbd` for the trace from `boundsFrom`. This remains true for empty arrays or other degenerate inputs.

### [`ESS.buCut_gradient_absorption`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUShortGradient.lean#L28-L102) — `lean-pool-0033`

Snippet: `samples/lean-pool/lean-pool-0033.lean`

- `(hκ : 0 ≤ buCutScalar κ z)` (theorem): With hM retained, the right-hand side is nonnegative. If buCutScalar κ z < 0, the left-hand side is nonpositive because Real.sqrt is nonnegative, so the conclusion holds directly; otherwise hκ follows and the existing proof applies. This also covers the zero case.
- `(hM : 0 ≤ M)` (theorem): The bound hderiv implies 0 ≤ M: choose j = 0 in Fin 3 and combine 0 ≤ |spatialPartial (buCutScalar κ) 0 z| with hderiv 0. The existing proof can use this derived bound wherever it uses hM.

### [`IsoGraph.Canon.individualize_refines`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Progress.lean#L192-L202) — `lean-pool-0038`

Snippet: `samples/lean-pool/lean-pool-0038.lean`

- `(hv : v < n)` (theorem): The conclusion remains true for any `v`: `individualize` uses `p.pos[v]!` only to choose the cell whose `cst` entries it updates, and the update preserves every existing cell start under `Part.WF`. If `v < n`, `hp.posLt` shows that position is in range; otherwise `hp.posSize` makes `p.pos[v]!` the out-of-bounds default `0`. For `n = 0` the refinement goal is vacuous; for `n > 0`, position `0` is valid. The proof can establish the `individualize_cst_getElemD` formula directly from `individualize_cst_eq` and `setCstFrom_getElemD`, using `hp` at the chosen position; on the updated interval, `hp.cellCst` says the old `cst` value is the cell start, so an old start cannot lie in the interval. The `Part.WF` hypothesis is still needed: without it, an arbitrary `cst` array can have a start inside the interval that individualization overwrites.

### [`TauCeti.DavisKahanExt.le_riccati_small_root_of_quadratic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Riccati/BoundedSharpEstimates.lean#L41-L89) — `lean-pool-0045`

Snippet: `samples/lean-pool/lean-pool-0045.lean`

- `(hb : 0 ≤ b)` (theorem): With hb deleted, split on b ≥ 0. In the other case put c = -b > 0 and u = -t. The quadratic hypothesis gives c(1 + u²) ≤ d*u, so u > 0 and c*u² - d*u + c ≤ 0. This implies d² - 4*c² ≥ 0 and u ≥ 2*c/(d + Real.sqrt (d² - 4*c²)); negating gives the desired bound on t. The stated root is then exactly -2*c/(d + Real.sqrt (d² - 4*c²)).
- `(hd : 0 < d)` (theorem): With hd deleted, hb and hsmall imply 0 ≤ 2*b < d, hence 0 < d. The original proof can then proceed with this derived positivity.
- `(hsmall : 2 * b < d)` (theorem): With hsmall deleted, split on whether 2*b < d. In that case use the original argument. Otherwise, hb and hd give d ≤ 2*b, hence d² - 4*b² ≤ 0. Mathlib defines Real.sqrt to be zero on nonpositive inputs (Real.sqrt_eq_zero_of_nonpos), so the right-hand side is 2*b/d ≥ 1; ht1 gives t < 1, proving the bound directly.

### [`NavierStokes.HeatedOutgoing.E_times_U`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/HeatedOutgoing.lean#L1197-L1206) — `lean-pool-0047`

Snippet: `samples/lean-pool/lean-pool-0047.lean`

- `(hX : 0 < X)` (theorem): The identity also holds for X ≤ 0. In that case X / switchRadius is nonpositive (switchRadius is positive by hXR), so Lean’s Real.log junk-value convention gives log = 0; hence HeatTailEdit.switch is sigma 0 = 0 and the multiplier is 1. Thus heatE equals OutgoingDilation.E there, including X = 0. For X > 0, the existing heatE_times_U proof applies. The patch term still vanishes by correction_times_U_zero, which requires hXR but not hX.

### [`EulerOrdinarySobolev.Evolution.gradient_logarithmic_envelope`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/OrdinaryEulerBKM.lean#L109-L141) — `lean-pool-0078`

Snippet: `samples/lean-pool/lean-pool-0078.lean`

- `(hC : 0 ≤ C)` (variable): This follows from `hW` and `hlog`, so the theorem can be proved without taking `hC`. Use the initial time `⟨0, le_rfl, hT⟩`, which exists even when `T = 0`. There, `U.gradientNormPath` is nonnegative (`gradientNormPath_nonneg`), and the factor `1 + ‖…‖ + W t * log (exp 1 + tensorNorm …)` is strictly positive: the norm and tensor norm are nonnegative, `hW` gives `W t ≥ 0`, and the logarithm is positive since its argument is at least `exp 1 > 1`. Thus `hlog` implies `0 ≤ C * positive`, hence `0 ≤ C`. Deriving this fact replaces every use of `hC` in the proof.

### [`MaxAddDegree.represents_zero_of_degree_lt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConwayRefinement/ConwayRefinement/Algebra/Valuation/DegreeRepresentatives.lean#L140-L143) — `lean-pool-0082`

Snippet: `samples/lean-pool/lean-pool-0082.lean`

- `[IsOrderedCancelAddMonoid M]` (variable): The statement only needs the degree and additive quotient constructions, which do not require this instance. To prove the class equality without it, unfold `homogeneousMk` using `homogeneousMk_apply`; `componentMk_eq_zero_iff` (which omits this instance) turns `h` into a zero component, and `DirectSum.of` maps zero to zero. The inequality field follows from `h.le`. This also covers the bottom-degree and zero cases, since the argument uses exactly the given strict inequality. The other instances are needed to form `ν : MaxAddDegree R M` or the ordered degree comparison.

### [`NavierStokes.SignedCopyBounds.local_mul`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SignedCopyBounds.lean#L91-L97) — `lean-pool-0090`

Snippet: `samples/lean-pool/lean-pool-0090.lean`

- `(hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)` (theorem): This can be deleted. At any point in the domain and cell where the conclusion needs a bound, `hf.bounds` with derivative order 0 gives a nonnegative norm bounded by the corresponding majorant, so that majorant is nonnegative there even if `w n x` itself is not. Use the two local majorants as the nonnegative constants in the bilinear jet estimate, then combine them with `majorant_mul`. Outside the cells the conclusion is vacuous; the argument also covers zero constants and zero weights.
- `(hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x)` (theorem): This can likewise be deleted: `hg.bounds` at derivative order 0 forces the corresponding majorant to be nonnegative at every domain-and-cell point relevant to the conclusion. The bilinear jet estimate and `majorant_mul` then give the product bound without global nonnegativity of `v`. Empty cells are vacuous, and zero constants or weights cause no exception.

### [`RS.kernelSubobject_tensorHom_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/KernelPow.lean#L729-L761) — `lean-pool-0091`

Snippet: `samples/lean-pool/lean-pool-0091.lean`

- `[Epi p₁]` (theorem): The inequality also holds for arbitrary p₁. Factor p₁ through its image, then use exactness of tensoring to apply the composite-kernel argument to that image factorization; the kernel of the first part is covered by imageSubobject (kernel.ι p₁ ▷ Z₂), and the remaining kernel is covered by imageSubobject (Z₁ ◁ kernel.ι p₂). The source’s tensorRight_preservesLimits and tensorRight_preservesColimits instances give the needed exactness in the rigid abelian setting. This argument also covers zero and other degenerate morphisms.
- `[MonoidalPreadditive A]` (theorem): This is used by the proof, not by the statement, and follows from the other assumptions: Abelian A is preadditive, while rigidity gives tensorLeft and tensorRight both limit- and colimit-preserving adjoints (as in tensorRight_preservesLimits, tensorRight_preservesColimits, and their tensorLeft counterparts). Thus they preserve finite biproducts and are additive, yielding MonoidalPreadditive A. The proof can install this derived instance; this reasoning also applies in the zero or trivial category.

### [`Egrs75.ClearingP3.lowDigits_half_pred_pow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Egrs75/SubtractBranch.lean#L172-L181) — `lean-pool-0093`

Snippet: `samples/lean-pool/lean-pool-0093.lean`

- `(hp : 3 ≤ p)` (theorem): Oddness alone suffices. For odd p, either p = 1 or 3 ≤ p. In the latter case the existing proof applies using that bound. If p = 1, then p^m = 1, so (p^m - 1) / 2 = 0, and RoundUp.lowDigits_zero gives the conclusion. Thus hp can be deleted, including the degenerate odd base p = 1.

### [`NFChoice.Compiler.NFCompactLeafFinalGate.axSiCompact`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NFWeakPartition/NFCompactLeafFinalGate.lean#L209-L255) — `lean-pool-0096`

Snippet: `samples/lean-pool/lean-pool-0096.lean`

- `(hzw : z ≠ w)` (theorem): When `z = w`, the two nested universal quantifiers in the conclusion use the same variable, so the conclusion only requires the diagonal case where both quantified values are equal. The literal `axSi` obtained from `hNF` supplies that case: after choosing the witness, specialize its two universal quantifiers to the same value. Thus the proof can use `hY Z Z` instead of translating arbitrary independent `Z` and `W`; no assumption excluding `z = w` is needed.

### [`NavierStokes.TerminalCompensation.physicalProfile_family_contDiffOn`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalCompensation.lean#L1082-L1099) — `lean-pool-0105`

Snippet: `samples/lean-pool/lean-pool-0105.lean`

- `(hR : 0 < R)` (theorem): The profile remains smooth without positivity of R. If R ≠ 0, then z.2 / R ≠ 0 on the domain, so Mathlib's `Real.contDiffAt_rpow_const_of_ne` gives the needed smoothness of the base profile; the correction is already smooth. If R = 0, the quotient is constantly 0, and the correction there vanishes because its support lies in `Icc P.left P.right` with `P.left > 0`. The profile then reduces to `a z.1 * baseProfile lam 0`, a smooth function. Thus the proof can split on whether R is zero and does not need `hR`.

### [`NavierStokes.PolarCharts.chart_finiteJets_uniform`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalGraphBounds.lean#L336-L354) — `lean-pool-0108`

Snippet: `samples/lean-pool/lean-pool-0108.lean`

- `(ha : 0 < a)` (theorem): The bound still holds for every real `a`: the proof can use smoothness of `chart a j` without requiring `a > 0`. For `a ≠ 0`, the first `positiveRadius` parameter `a ^ 2 / 32` is positive, so that coordinate is smooth after `sqrt`; the denominator `positiveRadius (a / 8) p.1` is nonzero even when `a < 0`. Indeed, with a negative parameter, the definition and `Real.smoothTransition`’s cutoff and range properties make this value negative. For `a = 0`, division by zero in the argument of `smoothTransition` gives zero, so `positiveRadius 0 x = 0`; `chart 0 j` is constant, and its jets are bounded. Thus in each case `chart a j` is smooth, and the existing compact-ball continuous-jet bound and finite sum argument prove the conclusion. The radius `b` may also be negative: then the closed ball is empty, which causes no exception.

### [`NavierStokes.SlowStressSupport.axial_stress_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SlowStressSupport.lean#L2093-L2133) — `lean-pool-0111`

Snippet: `samples/lean-pool/lean-pool-0111.lean`

- `(hn : 0 < n)` (theorem): The theorem statement and the supporting lemmas `smooth_axialDensity`, `axial_integral_zero`, and `exterior_axialDensity` are stated for arbitrary `n : ℕ`. In this proof, `hn` is used only to establish `n - 1 ≤ n`; that inequality holds unconditionally by `Nat.sub_le _ _`. Replacing the proof of `hprev_le` with that lemma removes the need for `hn`, including when `n = 0`.

### [`CKN.Leray.mildShiftedStokesIntegral_continuous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierMildIntegral.lean#L216-L225) — `lean-pool-0117`

Snippet: `samples/lean-pool/lean-pool-0117.lean`

- `(hC : 0 ≤ C)` (theorem): This follows from `hFC`: at `t = 0`, `‖F 0‖ ≤ C`, while `0 ≤ ‖F 0‖`. Thus the proof can derive `hC` by transitivity and use the existing argument unchanged.
- `(hT : 0 ≤ T)` (theorem): If `T < 0`, the interval from `0` to `T` lies where `τ ≤ 0`; there `mildShiftedStokesIntegrand F t τ = 0` for every `t`, so the integral is identically zero and hence continuous. If `0 ≤ T`, use the existing proof with that inequality. Thus `hT` can be removed.

### [`ESS.buGaussian_shifted_trace_strip_tendsto`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUGaussianAverageTools.lean#L334-L436) — `lean-pool-0118`

Snippet: `samples/lean-pool/lean-pool-0118.lean`

- `(hB : MeasurableSet B)` (theorem): The shift and inverse-map identities make the two integrands in `hprodEq` equal pointwise, not merely almost everywhere on the integration set. Thus those equalities can be proved with `integral_congr_ae` under the restricted measure, without requiring `B` measurable. `MeasurePreserving.setIntegral_image_emb` and `setIntegral_parabolic_to_product` also do not require measurability of the set. The shifted integral therefore equals the trace integral for every ε, and `htrace` proves the conclusion.

### [`NavierStokes.PressureStream.reconstructed_divergence_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PressureStream.lean#L773-L791) — `lean-pool-0120`

Snippet: `samples/lean-pool/lean-pool-0120.lean`

- `(hab : a < b)` (theorem): If `a < b` fails, then the support condition confines `γd` to the empty radial interval when `a > b`, or to the single radial slice `r = a` when `a = b`. In the latter case, continuity from `hγ` and vanishing off that slice force `γd = 0` as well. Thus `weightedSource γd` and hence `streamPotential` are zero, making the divergence conclusion immediate. When `a < b`, the existing proof applies. The binder is not needed to elaborate the statement.

### [`CKN.Core.HeatPotential.heatPotential_series_representation_of_morrey`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Core/HeatPotential/SubordinatedEnd.lean#L24-L142) — `lean-pool-0121`

Snippet: `samples/lean-pool/lean-pool-0121.lean`

- `(hq : q ∈ @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r)` (theorem): The conclusion should hold for any q. For each source, local integrability near q follows by applying `heatPotential_near_kernel_integrable` (or its spatial-kernel counterpart) with center q and radius 1, since q lies in its own closed ball. Away from that neighborhood the kernel is bounded, and compact support together with the Morrey assumptions gives source integrability via `heatPotential_source_integrable_of_compact_support`. Thus the integrands are integrable on the whole domain, allowing the same near/far integral decomposition and summability argument without requiring q to lie near z. The zero/junk cases do not obstruct this argument.

### [`GerverSofa.PartC.Stage2.rhoC_nonneg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MovingSofa/GerverSofa/KernelOnly/Core/Bundle006.lean#L896-L906) — `lean-pool-0129`

Snippet: `samples/lean-pool/lean-pool-0129.lean`

- `(ht : t ∈ Set.Icc (0 : ℝ) T)` (theorem): `rhoC t` is nonnegative for every real `t`. In the first branch it is `1/2`; in the last it is `0`. In the middle branches, the failed earlier conditions imply `t > params.phi`, so `0 ≤ t` follows from `Romik.phi_pos_of_mem_box params_mem` and `phi_nonneg`. The existing phase-2 and phase-3 nonnegativity lemmas then apply. In phase 4, the failed `t ≤ eta` condition gives `eta ≤ t`, and the branch condition supplies `t ≤ tau`, so `rhoC_phase4_nonneg` applies. Thus the proof can split on the same conditions without using `ht`; no out-of-range real values create an exception.

### [`AVenhance.Infra.Section5.Contracts.sds_gradMatrix_entry_periodic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/Contracts/TermCenteredAnalyticSmooth.lean#L49-L57) — `lean-pool-0130`

Snippet: `samples/lean-pool/lean-pool-0130.lean`

- `(hF : Differentiable ℝ F)` (theorem): The equivariance hypothesis alone gives the scalar component identity `F (y + latticeShift k) j = F y j + latticeShift k j`. The translation identity `fderiv_comp_add_right` and constant-addition identity `fderiv_add_const` show the component's derivatives at `x + latticeShift k` and `x` agree without assuming differentiability. These identities also handle nondifferentiable points, since translation preserves differentiability and `fderiv` is zero at such points. Thus the `gradMatrix` entry remains periodic for arbitrary `F` satisfying `he`, including degenerate cases.

### [`RS.LaurentTail.injG_apply_of_not_mem`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/LaurentTail/Comparison.lean#L1239-L1247) — `lean-pool-0131`

Snippet: `samples/lean-pool/lean-pool-0131.lean`

- `[T2Space X]` (variable): The statement and proof use only the topology on X and the given cover; neither requires the Hausdorff separation property. The included data and injG can be formed without T2Space, and the proof is unchanged.
- `[CompactSpace X]` (variable): Compactness is not used by the statement or proof: the argument reduces to the empty-intersection case for the conditional defining injG and contradicts hnot otherwise. The cover and included data can be formed without compactness, so the proof is unchanged.

### [`polytopeRoundedSupportCurve_regular`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OperatorTheory/Operator/Crouzeix/SmoothSupportCurve.lean#L231-L242) — `lean-pool-0133`

Snippet: `samples/lean-pool/lean-pool-0133.lean`

- `(hu : u.Nonempty)` (theorem): Split on whether `u` is empty. In the nonempty case, the existing proof applies. If `u` is empty, `polytopeSoftPartition` is identically `0`, so `Real.log 0 = 0` makes `polytopeSoftSupport` identically `0` and `polytopeRoundedSupport` identically `rho`. The curve is then `smoothSupportCurve` of the constant function `rho`; its curvature radius is `rho`, positive by `hrho`, so `smoothSupportCurve_regular` proves the conclusion. Thus the theorem remains true without `hu`. (The strict positivity of `delta` remains available for the nonempty case.)

### [`QuadraticCarleson.packetPoint_abs_sub_right_ge`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/CounterexampleGeometry.lean#L68-L86) — `lean-pool-0135`

Snippet: `samples/lean-pool/lean-pool-0135.lean`

- `(hN : 100 ≤ N)` (theorem): The estimate holds for every integer k, so hN is not needed, even while retaining hk. Put m = k.toNat. Since k ≤ m and j ≥ m + 1, we have k + τ ≤ j − 1/2 using hτ. Thus the absolute value is j − k − τ and is at least j − m − 1/2, which is the left side. For k ≥ 0, m = k; for k < 0, m = 0, and the same inequalities apply. This argument also covers the degenerate cases without relying on paperBohrIndex_cast_toNat.
- `(hk : k ∈ paperBohrIndices N)` (theorem): The estimate holds for every integer k, so hk is not needed, even while retaining hN. With m = k.toNat, use k ≤ m, hj, and τ ≤ 1/2 to see k + τ ≤ j − 1/2. Hence the absolute value is j − k − τ ≥ j − m − 1/2, equal to the left side. For k ≥ 0, m = k; for k < 0, m = 0, so the argument includes negative k as well.

### [`NavierStokes.PhysicalCoordinateBounds.xLift_homogeneous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalCoordinateBounds.lean#L421-L426) — `lean-pool-0136`

Snippet: `samples/lean-pool/lean-pool-0136.lean`

- `(_hy : y ∈ positiveTime)` (theorem): The proof does not use `_hy`. The identity holds for every `y`: after unfolding, it follows from `Real.rpow_zero` and `mul_div_mul_left` using only `hr.ne'`. This cancellation also holds when `y.1 = 0`, since real division by zero is defined as zero.

### [`NavierStokes.ActivationCone.natural_reference_bounds`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ActivationCone.lean#L819-L863) — `lean-pool-0138`

Snippet: `samples/lean-pool/lean-pool-0138.lean`

- `(hδlim : 2 * δ < ReferencePath.rampLimit)` (theorem): Only a collar near y = 0 is needed. Given hδ, choose a smaller positive width ε ≤ δ with ε < rampLimit. On that collar the continuation cutoff is identically one, so the reference fields and their radial derivatives agree locally with the natural fields; the natural smoothness and F.cone_margin at y = 0 supply the hypotheses for compact_reference_bounds on [0, ε] × Icc (-1) 1. Its resulting τ satisfies τ ≤ ε ≤ δ, and the conclusion uses the original δ-dependent A and B, which agree there with the natural quantities. Thus δ need not itself satisfy the ramp-limit bound.

### [`QuantumParallelRepetition.exactReverseAliceMarkedHistoryContext_fiber_iff`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuantumParallelRepetition/Part07.lean#L6721-L6744) — `lean-pool-0155`

Snippet: `samples/lean-pool/lean-pool-0155.lean`

- `[Fintype X]` (variable): The context and result use X only in function and product types, not in a finite enumeration. The definitions of `exactReverseAliceMarkedHistoryContext` and `finitePrefixMask` need no `Fintype X`; the proof can use the same projection-and-equality argument without this instance.
- `[Fintype Y]` (variable): Y is used as the type of `default` and in function types, but not in a finite enumeration. The context and masking definitions need no `Fintype Y`, so the equality argument remains valid without it.
- `[Fintype A]` (variable): A appears only in outcome and history function types here; the relevant context and history constructions require no `Fintype A`. The proof is based on projections and equality, so this instance can be omitted.
- `[Fintype B]` (variable): B appears only in outcome and history function types here; the relevant context and history constructions require no `Fintype B`. The proof is based on projections and equality, so this instance can be omitted.

### [`NavierStokes.TerminalStress.swirlCoefficient_contDiffAt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalStress.lean#L412-L420) — `lean-pool-0158`

Snippet: `samples/lean-pool/lean-pool-0158.lean`

- `(hh : 0 < h)` (theorem): This can be deleted while retaining `hh1`. If `h ≤ 0`, `SimilarityCoordinates.coordinateQ` takes its fallback value `1`, since its active branch requires `0 < 2 * h`. Thus `SimilarityProfile.X h p = p.2.1`; `hs` makes its logarithm smooth locally, and `hf` supplies the needed regularity of `f`. If `h > 0`, the remaining `hh1` gives the existing `flattening_contDiffAt` proof.
- `(hh1 : h < 1 / 2)` (theorem): This can be deleted while retaining `hh`. If `h ≥ 1 / 2`, `SimilarityCoordinates.coordinateQ` takes its fallback value `1`, since its active branch requires `2 * h < 1`. Hence `SimilarityProfile.X h p = p.2.1`; as `hs` gives `p.2.1 > 0`, composing `hf` with the locally smooth logarithm gives the required regularity. If `h < 1 / 2`, the remaining `hh` gives the existing `flattening_contDiffAt` proof.

### [`PDL.LoadedCluster.satDown_three_not_basic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/ClusterSatDown.lean#L575-L602) — `lean-pool-0171`

Snippet: `samples/lean-pool/lean-pool-0171.lean`

- `(hlen : next.length = (C.stepOfL Δ).length)` (theorem): `C.Q` is defined using `QuasiTab.build`. Every type-three node in that construction has children given by `(C.stepOfL Δ).map ...` (see `QuasiTab.build`), so the length equality follows from `hx` by inverting the build/atOpt construction. The proof can derive `hlen` from `hx` and use it for `hi'`; this remains true for empty lists as well.

### [`NavierStokesAndEuler.SmoothCutoff.cutoff_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/ForMathlib/SmoothCutoff.lean#L86-L90) — `lean-pool-0181`

Snippet: `samples/lean-pool/lean-pool-0181.lean`

- `(hR : 0 < R)` (theorem): If R > 0, the existing proof applies. Otherwise hx and 0 ≤ ‖x‖ imply R = 0 and ‖x‖ = 0, hence x = 0. Then cutoff E 0 0 = 1 because 0⁻¹ • 0 = 0 and baseCutoff_eq_one applies at the origin. Thus the conclusion also holds in the only nonpositive case allowed by hx.

### [`BooleanIsoperimetry.harper_macaulay_min`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L154-L176) — `lean-pool-0191`

Snippet: `samples/lean-pool/lean-pool-0191.lean`

- `(ha : a ≤ 2 ^ N)` (theorem): If `a ≤ 2 ^ N`, the existing theorem's proof applies using this bound and `hb`. Otherwise `simplicialInitSeg N a` is the whole cube: `card_simplicialInitSeg` gives its cardinality as `min a (2 ^ N) = 2 ^ N`, so its neighborhood is also the whole cube and `H N a = 2 ^ N`. Then `H_le_cube` bounds the left side by `2 ^ (N + 1)`, while the right side is at least `H N a + a = 2 ^ N + a > 2 ^ (N + 1)`. Thus `ha` can be deleted without changing the conclusion.
- `(hb : b ≤ 2 ^ N)` (theorem): Symmetrically, if `b ≤ 2 ^ N`, the existing theorem's proof applies using `ha`; otherwise `card_simplicialInitSeg` shows `H N b = 2 ^ N`, and the right side is at least `b + H N b > 2 ^ (N + 1)`, whereas `H_le_cube` bounds the left side by `2 ^ (N + 1)`. Thus `hb` can be deleted without changing the conclusion.

### [`PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PebblingLean/UpperBoundParameters.lean#L2099-L2138) — `lean-pool-0205`

Snippet: `samples/lean-pool/lean-pool-0205.lean`

- `(hsmall : splitM K n < n)` (theorem): This follows from `hslack`. If `n ≥ 2` and `splitM K n ≥ n`, then `splitA K n = n - splitM K n = 0`, so `hslack` would imply `1 ≤ loss n = 1/(n^2)`, which is false. If `n = 0`, `hslack` is impossible since `loss 0 = 0`. If `n = 1`, the definition `splitM K 1 = ⌈K * sqrt (log 1)⌉₊` gives `splitM K 1 = 0`, hence `splitM K 1 < 1`. Thus `hsmall` can be derived, and the proof can use this derived fact wherever it currently uses `hsmall`.

### [`AleksandrovDifferentiability.prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/AleksandrovDifferentiability/Analysis/GoodSet.lean#L97-L106) — `lean-pool-0218`

Snippet: `samples/lean-pool/lean-pool-0218.lean`

- `[SFinite ν]` (theorem): This can be deleted: from `hsection`, each vertical section of `s \ G` is `ν`-null, and any measurable set `t` witnessing the null-measurable representation of `s \ G` has sections contained in those null sections. Apply Mathlib's `Measure.measure_prod_null_of_ae_null`, which only requires measurability of `t` and does not require `[SFinite ν]`, then transfer the result back using the almost-everywhere equality from `hbad`. Thus the conclusion also holds in the degenerate cases without s-finiteness.

### [`Zeta5Irrational.cov_302_304`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta5Irrational/Table/Intervals.lean#L7296-L7302) — `lean-pool-0219`

Snippet: `samples/lean-pool/lean-pool-0219.lean`

- `(0 < t)` (theorem): The lower-bound hypothesis already implies positivity: the rational `723732917263 / 2560000000000` is positive, so `lt_of_lt_of_le (by norm_num) h1` supplies `0 < t`. The proof can use this derived fact in place of `h0` in both `tc_302` and `tc_303`; thus the positivity implication can be deleted.

### [`TauCeti.DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_reducingSubspace`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/SinTheta/Natural/Reducing.lean#L496-L543) — `lean-pool-0223`

Snippet: `samples/lean-pool/lean-pool-0223.lean`

- `(hAdense : Dense (A.domain : Set ER))` (theorem): It follows from the retained `(hA : IsSelfAdjoint A)` as `hA.dense_domain`. The proof can use that derivation when constructing the complementary restriction’s self-adjointness; the result theorem needs no independent density assumption.
- `(hAclosed : A.IsClosed)` (theorem): It follows from the retained `(hA : IsSelfAdjoint A)` as `hA.isClosed`. The `UnboundedSinThetaData` core explicitly omits closedness fields, and the result can be proved without this separate argument.
- `(hA0dense : Dense (A0.domain : Set FR))` (theorem): It follows from the retained `(hA0 : IsSelfAdjoint A0)` as `hA0.dense_domain`. The proof can construct the needed data and invoke the exact real theorem using the self-adjointness-derived density.
- `(hA0closed : A0.IsClosed)` (theorem): It follows from the retained `(hA0 : IsSelfAdjoint A0)` as `hA0.isClosed`. The exact real result uses self-adjointness, not an independent closedness assumption; the data can be built without this redundant argument.

### [`BGS.CorvajaZannier.exists_support_direction_of_not_rankTwo`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveSupportRank.lean#L186-L216) — `lean-pool-0224`

Snippet: `samples/lean-pool/lean-pool-0224.lean`

- `(hnonsingleton : ∃ s ∈ f.support, s ≠ r)` (theorem): If some support exponent differs from `r`, the existing argument applies: its exponent difference is nonzero, and `hnrank` forces every other support difference to have determinant zero with it, so `integerVectorLine_cyclic` gives the required nonzero direction. If no support exponent differs from `r`, then every `s ∈ f.support` equals `r`; choose any nonzero vector, such as `(1, 0)`, and use `k = 0` for every `s`. This also covers the singleton-support case; `hr` rules out empty support.

### [`ViscositySolns.SmoothConvexApproximationOnInteriorClosedBallTheorem.of_extensionMollification`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Jensen/ConvexMollification.lean#L285-L308) — `lean-pool-0232`

Snippet: `samples/lean-pool/lean-pool-0232.lean`

- `(hmoll : ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem n)` (theorem): The conclusion can be proved without assuming the packaged mollification theorem. First use `exists_continuous_extension_eqOn_intermediate_closedBall_of_convexOn_closedBall` to extend `g` continuously on an intermediate ball of radius `Rmid` with `r < Rmid < R`. Then take `gseq m` to be convolution of that extension with the bump `jensenMollifierBump` at a fixed positive radius `rho ≤ Rmid - r`. The existing lemmas `contDiff_two_normedBumpConvolution_left`, `convexOn_normedBumpConvolution_of_convexOn_extension`, and `exists_pos_forall_rOut_le_abs_normedBumpConvolution_sub_extension_le` give, respectively, smoothness, convexity on the smaller ball, and eventual uniform approximation; `tendsto_jensenMollifierBump_rOut` supplies the required index bound for approximation. These arguments also apply in degenerate dimensions, so no extra nonemptiness or nonzero assumption is needed.

### [`CarlsonFunctions.SeveralComplexVariables.norm_sub_le_of_separately_analytic_bounded`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CarlsonFunctions/SeveralComplexVariables/LocallyBounded.lean#L67-L108) — `lean-pool-0237`

Snippet: `samples/lean-pool/lean-pool-0237.lean`

- `(hr : 0 < r)` (theorem): The theorem remains true for all real r. If r < 0, `closedBall c r` is empty since distances are nonnegative, contradicting hx. If r = 0, hx and hy force x = c = y, so the left side is 0; the right side is also 0 because `M / 0 = 0` (and `‖y - x‖ = 0`). For r > 0 the given proof applies unchanged. Thus hr is only needed for that proof, not the statement.

### [`TriangleInflation.Peps_tminAI_bounds`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/InflationTermination/TriangleInflation/Exponent.lean#L334-L351) — `lean-pool-0238`

Snippet: `samples/lean-pool/lean-pool-0238.lean`

- `(h0 : 0 < ε)` (theorem): At ε = 0, which is allowed by h1 alone, Real.zero_rpow gives 0 raised to the nonzero exponents in the statement and in Peps. Thus the lower bound's left side is 2. But Peps 0 = Q 0 1 is the deterministic law concentrated on (true, true, true). For every t, the point mass at the all-true assignment witnesses AIFeasible t (Peps 0): its diagonal law is the tensor power of that deterministic law, and its injectable marginals and ancestral products are the corresponding deterministic laws. Hence the rejecting-order set defining tminAI is empty, so by Nat.sInf its value is 0; the lower bound fails. Therefore h0 cannot be deleted.

### [`LeanPool.Besicovitch.sigma_mul_radius_div_two_le_diam_localAttachmentComponent`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Besicovitch/Rectifiability/ComponentDiameter.lean#L38-L191) — `lean-pool-0244`

Snippet: `samples/lean-pool/lean-pool-0244.lean`

- `(hrho : 0 < rho)` (theorem): The nonempty annulus supplies a point w with dist z w < rho. Since dist z w ≥ 0, this implies 0 < rho. Use this derived fact wherever hrho is used, including to show z lies in the closed ball and in the ENNReal.ofReal comparison.
- `(hsigma_one : sigma < 1)` (theorem): The annulus supplies w with dist z w < rho and w not in Metric.ball z (sigma * rho / 2), hence sigma * rho / 2 ≤ dist z w < rho. This directly gives the hR_rho bound needed by the proof, so hsigma_one can be deleted. The remaining density estimate uses hsigma and hsigma_gamma, not hsigma_one.

### [`Zeta5Irrational.tc_361`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta5Irrational/Table/Intervals.lean#L2671-L2676) — `lean-pool-0249`

Snippet: `samples/lean-pool/lean-pool-0249.lean`

- `0 < t` (theorem): The lower bound implies `0 < t`, since `46687825988961 / 128000000000000` is positive. Without this implication, positivity can be derived from the lower-bound hypothesis (for example, by `norm_num` and `linarith`) and used in the proof. The other bounds and conclusion are unchanged.

### [`CKN.norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Poincare/Lp.lean#L159-L202) — `lean-pool-0254`

Snippet: `samples/lean-pool/lean-pool-0254.lean`

- `(hu : MeasureTheory.IntegrableOn u U)` (theorem): From `huDiff`, the pointwise segment estimate bounds `‖u x - u y‖` by the integrable function in `hsegment`. Continuity gives the measurability needed for integrable domination, so `u x - u` is integrable on `U`. The finite-measure assumption makes the constant function `u x` integrable; hence `u` is integrable as their difference. This derived integrability supplies the hypothesis used by `norm_sub_integralAverage_le_volumeAverage_integral_norm_sub`. The positive-volume assumption rules out the zero-volume normalization issue.

### [`NRR.Geometry.ConvexBody.neg_carrier`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NandakumarRamanaRao/NRR/Geometry/ConvexBody/SupportFunctionTransform.lean#L107-L108) — `lean-pool-0259`

Snippet: `samples/lean-pool/lean-pool-0259.lean`

- `[NormedAddCommGroup E]` (variable): This can be omitted: `[InnerProductSpace ℝ E]` supplies the seminormed additive group, topology, and real module structure needed to form `ConvexBody E` and its carrier. The equality is definitional (`rfl`) for every `K`, so the degenerate cases do not require an additional assumption.

### [`EGZ.CommonMeasure.final_mass_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ErdosGinzburgZiv/EGZ/Decomposition/CommonMeasure.lean#L109-L119) — `lean-pool-0276`

Snippet: `samples/lean-pool/lean-pool-0276.lean`

- `(hR : 0 < R)` (theorem): It can be deleted. From `hu` and `hle`, `w a` is nonnegative for every `a`, so `mass w P` is nonnegative; with `hP`, this gives `0 ≤ R`. If `R > 0`, use the existing proof. If `R = 0`, then `mass w P = 0`; since `0 ≤ u a ≤ w a`, `mass u P = 0`, while `hu` gives `0 ≤ mass u Q`. Thus the conclusion holds, including when the type is empty. This handles the zero case without `hR`; negative `R` is impossible under the other hypotheses.

### [`eigenvector_constant_sign`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SpectralPositivity/Operator/JentzschProof.lean#L332-L387) — `lean-pool-0280`

Snippet: `samples/lean-pool/lean-pool-0280.lean`

- `(hT_compact : IsCompactOperator T)` (theorem): The proof passes this only to `abs_eigenvector_of_top_eigenvector`, whose corresponding binder is named `_hT_compact` and is unused. The helper's proof does not need compactness, so that binder can be removed and the helper called without `hT_compact`; the rest of this theorem's argument is unchanged. This does not depend on nontriviality or nonemptiness of the space.

### [`QuadraticCarleson.annularQuadraticKernel_correlation_le_ordered`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/QuadraticFixedHeightAveragingCorrelation.lean#L49-L127) — `lean-pool-0281`

Snippet: `samples/lean-pool/lean-pool-0281.lean`

- `(hD : 0 ≤ D)` (theorem): This follows from the other hypotheses: `hab 0` gives `‖a 0‖ ≤ D / R`, while `0 ≤ ‖a 0‖` and `hR : 0 < R` imply `0 ≤ D`. The proof can derive `hD` this way and use it in place of the explicit assumption; the conclusion is unchanged.

### [`AVenhance.Infra.Section3.ChiMKCorrector.chiMK_spaceLap_three_active`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section3/ChiMKCorrector.lean#L159-L209) — `lean-pool-0282`

Snippet: `samples/lean-pool/lean-pool-0282.lean`

- `(hk : k % 4 = 3)` (theorem): The identity holds for every k. When k % 4 = 3, the active-component calculation proves it. Otherwise, the 0th component of `uShear` is zero by its definition: it is zero in the k % 4 = 1 case and also when neither active residue applies. Thus `I.chiMK κ m k t · 0` is identically zero, and `ChiMKCorrector.chiMK_spaceLap_of_zero_component` proves the identity, including the zero right-hand side. The proof can split on whether k % 4 = 3, using the existing active calculation in that branch.

### [`Malliavin.memLp_mderiv_cylinder_expGrowth`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/CylindricalGrowth.lean#L488-L496) — `lean-pool-0295`

Snippet: `samples/lean-pool/lean-pool-0295.lean`

- `(hC : 0 ≤ C)` (theorem): This follows from the other hypotheses: evaluate `hfg'` at the zero coordinate vector. The derivative norm is nonnegative and the right side is `C`, so `0 ≤ C`. Thus the existing proof can obtain `hC` and use `expGrowth_coord_le` as before.
- `(hc : 0 ≤ c)` (theorem): For `c < 0`, retain `hC` and use `‖y‖ ≥ 0` to get `C * exp (c * ‖y‖) ≤ C`; hence `hfg'` bounds the derivative by the constant `C`. The pointwise bound `norm_mderiv_cylinder_le` then bounds the Malliavin derivative by `C * ∑ i, ‖ofDual μ (L i)‖`. This constant has integrable square since `IsGaussian μ` supplies `IsProbabilityMeasure μ`, so `memLp_of_le_of_integrable_sq` proves the result. For `c ≥ 0`, use the existing exponential-growth proof. This also covers `C = 0` and `n = 0`.

### [`Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_of_generated`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/BrownianPurePowerDuality.lean#L393-L402) — `lean-pool-0298`

Snippet: `samples/lean-pool/lean-pool-0298.lean`

- `(hsm : ∀ t, StronglyMeasurable (B t))` (theorem): This follows from `coordinate_apply`: for each t, `B t` is the function `w ↦ coordinate t w`, which is continuous because `coordinate t : StrongDual ℝ W`. Since W has its Borel measurable space, a continuous real-valued function is strongly measurable. Thus hsm can be derived and supplied to the existing proof; the conclusion and all degenerate cases are unchanged.


## FLT (Anthropic) (60 flagged)

### [`P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.C2idemCore.IdempotentOrbit.exists_idempotent_orbit_or_isField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.lean#L172-L278) — `flt-anthropic-0014`

Snippet: `samples/flt-anthropic/flt-anthropic-0014.lean`

- `[Finite ι]` (variable): This can be removed: if ι is empty, the empty product is subsingleton and the first disjunct holds. If ι is nonempty, periodicity of s makes its conjugate on the product periodic too; the source’s `exists_indexMap_of_iterate_eq` construction yields a coordinate map ψ with ψ^[n] = id. The finite ψ-orbit S of any coordinate is nonempty and invariant, so ind S corresponds under φ to an idempotent fixed by s. By hfix it lies in the image of f, and an idempotent in the image of a field homomorphism into the nontrivial ring R must be 0 or 1. Since S is nonempty, ind S is not 0, hence it is 1, forcing S to contain every coordinate. Thus ι is finite after all. In the theorem without [Finite ι], this argument supplies a `Finite ι` instance in the nonempty case; the existing proof then applies.

### [`P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6.comp_heckeDiag_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.lean#L664-L678) — `flt-anthropic-0018`

Snippet: `samples/flt-anthropic/flt-anthropic-0018.lean`

- `(hp : p ≠ 0)` (theorem): The excluded case p = 0 also satisfies the conclusion: `ModularForm.heckeDiagMatrix_zero` gives `heckeDiagMatrix 0 = 1`, so its action is the identity and the composed function is F, which is nonzero by hF. For p ≠ 0, the existing proof applies. Thus a proof without hp can split on p = 0 and use these two cases.

### [`P2MW.S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.Blk176Arith.not_cube_dvd_mul_prod_filter`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.lean#L147-L182) — `flt-anthropic-0038`

Snippet: `samples/flt-anthropic/flt-anthropic-0038.lean`

- `(hN0 : N ≠ 0)` (theorem): This follows from `hN3`: if `N = 0`, then `2` is prime and `2 ^ 3 ∣ N` (every natural number divides zero), contradicting `hN3 2 Nat.prime_two`. The proof can first derive `hN0` this way, then use it at the existing factorization steps. Thus the case `N = 0` is already excluded by the remaining hypotheses.

### [`P2MW.S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.WeierstrassCurve.Affine.isPrincipal_of_geomDivisorSum_eq_zero'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_genusOnePlaceGate_isCentred_and_abelTheorem.lean#L2026-L2070) — `flt-anthropic-0040`

Snippet: `samples/flt-anthropic/flt-anthropic-0040.lean`

- `[DecidableEq F]` (variable): The theorem's statement— including `Divisor.degree` and `geomDivisorSum`—does not require decidable equality on `F`. The proof already begins with `classical`, which supplies the needed decidable equality for its finite-support operations, so the theorem remains provable after deleting this variable hypothesis.

### [`P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.P2mS17LB.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.lean#L49-L111) — `flt-anthropic-0046`

Snippet: `samples/flt-anthropic/flt-anthropic-0046.lean`

- `(hn : 0 < n)` (theorem): The other hypothesis `hα` already forces `n > 0`: if `n = 0`, then `α ^ n = 1`, so `hα` would give `1 = (q : AlgebraicClosure ℚ)`, impossible since `q` is prime and the natural-number cast into this characteristic-zero field is injective. Thus the proof can derive `hn` from `hα` and use it wherever needed; the excluded case `n = 0` cannot occur.

### [`P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.PLCDSol.exists_gamma0_apply_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.lean#L883-L889) — `flt-anthropic-0048`

Snippet: `samples/flt-anthropic/flt-anthropic-0048.lean`

- `[NeZero M]` (variable): The conclusion also holds when M = 0. In that case ZMod 0 is ℤ, so a unit d has an integer representative whose inverse times itself is 1. The upper-triangular matrix with diagonal entries d⁻¹ and d and lower-left entry 0 has determinant 1, lies in Gamma0 0, and its top-left entry modulo 0 is d⁻¹ rather than d; instead use diagonal entries d and d, whose determinant is d² = 1 and whose top-left entry is d. Thus the zero-modulus case can be handled directly, while for M ≠ 0 the existing CohCarrier.gamma0Units_surjective proof supplies the witness.

### [`P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.CohCarrier.gammaH_inf_gamma0_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.lean#L104-L128) — `flt-anthropic-0049`

Snippet: `samples/flt-anthropic/flt-anthropic-0049.lean`

- `[NeZero N]` (theorem): This is implied by the remaining `[NeZero (N * ℓ)]`: since a product of naturals is nonzero, `N` is nonzero, so a local `NeZero N` instance can be derived. The statement and proof can then proceed unchanged.
- `[NeZero (N * ℓ)]` (theorem): The equality also holds when `ℓ = 0` (the only additional case, given `[NeZero N]`). `Gamma0` and `GammaH` are defined at modulus 0; `Gamma0_mem` identifies membership with the lower-left entry being zero in `ZMod 0`, and the cast/comap argument in the proof still applies. Thus this instance can be removed without changing the statement.

### [`P2MW.S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.ModularCurve.CupPairing.Shapiro.b_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.lean#L287-L288) — `flt-anthropic-0052`

Snippet: `samples/flt-anthropic/flt-anthropic-0052.lean`

- `[Γ.FiniteIndex]` (variable): `Potentials Γ f` and the conclusion do not require finite index. The proof can be rebuilt without it: `cfun_mul_mem` uses only quotient invariance for elements of Γ, and the `S`/`T` invariance argument used to prove `a_mul_sub_eq` is group-theoretic (`eq_apply_one_of_S_U`), with neither requiring `[Γ.FiniteIndex]`. Then `b_mul_sub_eq` and `phi_apply` give the stated result. The argument also covers trivial or empty quotient cases; no finiteness property is needed.

### [`TateCurve.pointX_inv_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_TateCurve_XMultStructure.lean#L171-L175) — `flt-anthropic-0057`

Snippet: `samples/flt-anthropic/flt-anthropic-0057.lean`

- `(hu0 : u ≠ 0)` (theorem): If u = 0, both arguments to pointX are 0, so the conclusion is reflexive; if u ≠ 0, the existing hv0 and hdiv allow the proof via pointX_inv. Thus hu0 can be deleted while leaving the other hypotheses unchanged.
- `(hv0 : v ≠ 0)` (theorem): If v = 0, both arguments to pointX are 0, so the conclusion is reflexive; if v ≠ 0, the existing hu0 and hdiv allow the proof via pointX_inv. Thus hv0 can be deleted while leaving the other hypotheses unchanged.

### [`P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.Nat.not_mem_placesOf_of_mem_placesOf_of_coprime`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.lean#L72-L74) — `flt-anthropic-0058`

Snippet: `samples/flt-anthropic/flt-anthropic-0058.lean`

- `(hℓ : ℓ ≠ 0)` (theorem): If ℓ = 0, `placesOf 0 = ∅` by its definition and `Ideal.span_singleton_eq_bot`, so `hv` is impossible. Otherwise the existing proof applies with `hℓ` supplied by the case split. Thus this hypothesis can be deleted.
- `(hℓ' : ℓ' ≠ 0)` (theorem): If ℓ' = 0, `placesOf 0 = ∅`, so the conclusion is immediate. Otherwise the existing proof applies with `hℓ'` supplied by the case split. Thus this hypothesis can be deleted.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L610-L612) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- `[CharZero L]` (variable): The equation only concerns the constant Laurent series: `HahnSeries.C_apply` reduces it to `HahnSeries.single 0 c`, and `algebraMap_laurentSeries_eq_single` identifies the algebra-map side with the same series. That lemma requires `[Field L]`, but not `[CharZero L]`; no degenerate field case is excluded by removing characteristic zero.

### [`P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.W8O.ramificationIndex_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.lean#L169-L198) — `flt-anthropic-0064`

Snippet: `samples/flt-anthropic/flt-anthropic-0064.lean`

- `[CharP M p]` (variable): This instance is implied by the remaining assumptions: since M and E are fields, algebraMap M E is injective, and Mathlib's Algebra.charP_iff gives CharP M p from CharP E p. A proof can locally derive the instance and then use the existing argument; the theorem statement itself does not require CharP M p.

### [`P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.lean#L2414-L2438) — `flt-anthropic-0066`

Snippet: `samples/flt-anthropic/flt-anthropic-0066.lean`

- `(ha2 : a ^ (q ^ 2) = a)` (theorem): `ha2` is not used in the conclusion or proof. The proof closes by applying `ModularCurve.C4b.core θ f h₁ h₁F h₁0 a ha hsupp`, which does not require `ha2`; removing it leaves the theorem provable with the same conclusion.

### [`P2MW.S_CohCarrier_isEis_kernel_pair_of_prime.CohCarrier.IsEisKernelPairPrime.exists_crt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_isEis_kernel_pair_of_prime.lean#L359-L443) — `flt-anthropic-0072`

Snippet: `samples/flt-anthropic/flt-anthropic-0072.lean`

- `[NeZero P]` (theorem): `mapN` is defined without a `NeZero` requirement. If `P = 0`, coprimality forces `M₁ = 1`; choose `g₁ = g`. The first equality is reflexive, and the second holds because `ZMod 1` is trivial.
- `[NeZero M₁]` (theorem): `mapN` is defined without a `NeZero` requirement. If `M₁ = 0`, coprimality forces `P = 1`; choose `g₁ = 1`. The first equality holds because `ZMod 1` is trivial, and the second is `map_one`, including when the target is `ZMod 0`.

### [`P2MW.S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.Loc4Sol.residual_isEquiv_point`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.lean#L165-L200) — `flt-anthropic-0088`

Snippet: `samples/flt-anthropic/flt-anthropic-0088.lean`

- `(hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)` (theorem): This is only used to apply the Frobenius comparison at primes outside S. Without hNS, instead exclude the finite set `S ∪ N.primeFactors` in `GaloisRepAdic.charpoly_eq_of_charpoly_frobenius_eq`. For any prime outside that union, it is outside S and does not divide N, so the existing `hθ` and `hρ'` hypotheses give the same characteristic-polynomial comparison. The library uses this enlarged-exception-set argument elsewhere (for example, with `S ∪ N.primeFactors` at lines 2151–2154 of `S_CuspForm_heckeLocal_bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd.lean`). The `[NeZero N]` assumption ensures the prime-factor exclusion works; no assumption about S containing the prime divisors of N is needed.

### [`P2MW.S_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq.LanglandsTunnell.CubicInduction.UnipotentEntryHaar.isAddHaarMeasure_map_entry`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_measure_unipotentEntry_preimage_mul_eq.lean#L119-L129) — `flt-anthropic-0092`

Snippet: `samples/flt-anthropic/flt-anthropic-0092.lean`

- `[BorelSpace (GL (Fin 2) K)]` (variable): The statement's measure and Haar-measure types require the measurable-space instance on `GL (Fin 2) K`, which remains separately available, but they do not require its `BorelSpace` instance. The proof can avoid the `OpensMeasurableSpace` source requirement of `Continuous.isOpenPosMeasure_map`: for an open set in `K`, use `map_apply` with `continuous_entry.measurable` and `BorelSpace K`, then apply `μN`'s open positivity to its open preimage. The compact-finiteness argument via the homeomorphism and left-invariance do not need `BorelSpace (GL (Fin 2) K)` either.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.K45VolB3.iterate_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.lean#L218-L220) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- `[NumberField L]` (variable): This instance is not needed by the statement or proof: `sigmaTensor` is defined for fields with an algebra, and the proof uses `sigmaTensor_pow` and `map_mul`, which require no number-field assumption on L. Removing `[NumberField L]` leaves the claim valid for any field extension L/K; no special or degenerate case is excluded.

### [`P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD.pairF_res_cores_normal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_index_Gamma_four.lean#L5591-L5659) — `flt-anthropic-0095`

Snippet: `samples/flt-anthropic/flt-anthropic-0095.lean`

- `[Γ'.FiniteIndex]` (theorem): The conclusion only uses `Γ'` in `res` and `Subgroup.relIndex`, which are defined without finite index. Since `Φ` has finite index in `SL(2, ℤ)` and `Φ ≤ Γ'`, the quotient `Γ' ⧸ Φ.subgroupOf Γ'` is finite: its cosets inject into `SL(2, ℤ) ⧸ Φ`. Thus the proof can obtain its `Fintype` from `[Φ.FiniteIndex]` and `hΦΓ`; no assumption that `Γ'` itself has finite index is needed.
- `(hΦ1 : (-1 : SL(2, ℤ)) ∉ Φ)` (theorem): `Φ` is a free group, hence torsion-free: Mathlib gives `FreeGroup` unique roots (`GroupTheory/FreeGroup/CyclicallyReduced.lean`), and `IsFreeGroup` identifies `Φ` with a free group. If `-1` belonged to `Φ`, its square would be `1`, so unique roots would force it to equal `1`; but `-1 ≠ 1` in `SL(2, ℤ)`. The proof can derive this fact from `[IsFreeGroup Φ]` and use it in place of `hΦ1` when applying `pairF_transport`.

### [`P2MW.S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.lean#L99-L202) — `flt-anthropic-0099`

Snippet: `samples/flt-anthropic/flt-anthropic-0099.lean`

- `(hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)` (theorem): The proof does not use `hcover`, and it does not occur in the conclusion or any later binder. Deleting it leaves the statement and proof steps unchanged.
- `(hred : IsReduced (pullback i₁.1 i₂.1))` (theorem): The proof does not use `hred`, and it does not occur in the conclusion or any later binder. The finiteness argument instead uses `hn` and `hn0`; deleting `hred` leaves the statement and proof steps unchanged.

### [`P2MW.S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift.P2mTwistedShiftDescent.exists_straighten`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_continuousMulEquiv_sigmaCentralizer_homeomorph_measurePreserving_twistedShift.lean#L314-L368) — `flt-anthropic-0108`

Snippet: `samples/flt-anthropic/flt-anthropic-0108.lean`

- `[SecondCountableTopology G]` (variable): The conclusion and construction need continuity and Borel measurability, but not second countability. The proof's measure-preserving step uses `exists_measurableEquiv_measurePreserving_pi_apply_succ_eq_inv_mul_mul`, whose hypotheses require a measurable group, sigma-finiteness, and left invariance, but not second countability. The remaining steps use the topological-group structure and continuity of the coordinate formulas. Thus the same construction works without this instance, including for trivial or empty-coordinate cases.

### [`P2MW.S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual.HopfTransfer.comulAlgHom_eq_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_bialgHom_surjective_etale_cartierDual_forall_existsUnique_comp_eq_of_bialgHom_injective_cartierDual.lean#L40-L43) — `flt-anthropic-0120`

Snippet: `samples/flt-anthropic/flt-anthropic-0120.lean`

- `[CommRing D]` (variable): The statement and proof only need D to be a semiring with its R-coalgebra structure: `HopfAlgebra R D` supplies those via its `Bialgebra` parent. `Coalgebra.Repr` also needs only the additive/module and coalgebra structures. Thus the theorem and its proof go through without `[CommRing D]`; the remaining `HopfAlgebra R D` supplies the required semiring instance.

### [`P2MW.S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.lean#L32-L223) — `flt-anthropic-0121`

Snippet: `samples/flt-anthropic/flt-anthropic-0121.lean`

- `(hpS : p ∈ S)` (theorem): The later hypothesis `hpN : p ∣ N`, together with `hNS` and `Fact.out : p.Prime`, yields `p ∈ S` directly via `hNS p Fact.out hpN`. The proof can pass this derived membership wherever it currently uses `hpS` (including the helper theorem); no degenerate case is excluded, since the derivation applies whenever the remaining hypotheses hold.

### [`P2MW.S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.NumberField.AdelicFourier.GodementSiegelEstimate.real_bound`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.lean#L337-L423) — `flt-anthropic-0123`

Snippet: `samples/flt-anthropic/flt-anthropic-0123.lean`

- `(hC : 0 ≤ C)` (theorem): This can be removed by splitting on `0 ≤ C`. In that case the existing proof applies. If `C < 0`, all the other factors on the left are nonnegative: `r, α, δ > 0` make the inverse powers nonnegative, and the `min` terms are nonnegative. Thus the left side is at most zero. Taking `B = 0` gives the required bound, since the right side is zero. The remaining hypotheses, in particular `c > 0`, still ensure `H > 0`; no degenerate case affects this argument.

### [`P2MW.S_TateCurve_ks17_D3_exports.TateCurve.sum_mul_Fz_Fz_eq_sum_lines_nat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_ks17_D3_exports.lean#L108-L111) — `flt-anthropic-0124`

Snippet: `samples/flt-anthropic/flt-anthropic-0124.lean`

- `[IsUltrametricDist K]` (theorem): This is only a regrouping of a finite sum by the values of g and h; it does not require an ultrametric. The statement still elaborates from [NontriviallyNormedField K], which supplies the Field structure required by Fz. A proof can regroup terms by those fibers and use Fz u 0 = Fz v 0 = 0 to account for the omitted zero indices. This also handles N = 0, when the bounds force g = h = 0 on S and both sides vanish.
- `[CompleteSpace K]` (theorem): Completeness is not used by the finite-sum regrouping, and Fz is algebraically defined for a Field. The same fiberwise regrouping proof works without this instance; zero-index terms vanish by Fz u 0 = Fz v 0 = 0, including the degenerate case N = 0.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal.Ψ₂Sq_𝓦p_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L273-L277) — `flt-anthropic-0125`

Snippet: `samples/flt-anthropic/flt-anthropic-0125.lean`

- `(hp2 : p ≠ 2)` (theorem): The excluded case is p = 2. There, the coefficient of X^3 vanishes, but Mathlib defines Ψ₂Sq as 4X^3 + b₂X^2 + 2b₄X + b₆ (DivisionPolynomial.Basic, `Ψ₂Sq`). For 𝓦p 2 over ZMod 2, b₂ = X 0 ^ 2, which is nonzero since MvPolynomial over the field ZMod 2 is a domain and X 0 is nonzero. Thus the coefficient of X^2 is nonzero, so the polynomial is nonzero. A proof can split on p = 2: use that coefficient argument in this case, and retain the existing coefficient-of-X^3 argument for p ≠ 2.

### [`P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.KcSemiLocalIwasawaHaar.mem_K_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean#L1008-L1009) — `flt-anthropic-0126`

Snippet: `samples/flt-anthropic/flt-anthropic-0126.lean`

- `[NumberField L]` (variable): The statement and proof do not require L to be a number field. The source confirms the same semi-local integral-set expressions can be used without this instance: `one_mem_semiLocalIntegralSet` is stated under `omit [NumberField L]`. Here `Iff.rfl` proves the characterization directly from the definitions, without using the number-field structure on L.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.AlgebraicCurve.HolRingFGAux.exists_fin_generators`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.lean#L590-L610) — `flt-anthropic-0132`

Snippet: `samples/flt-anthropic/flt-anthropic-0132.lean`

- `(hN : N.Nonempty)` (theorem): If `N` is empty, the condition on `f` says it belongs to every place valuation subring. In a function field of a curve over an algebraically closed field, every nonconstant element has a pole at some place, so such an `f` must lie in `k`. Take `n = 0` and the empty generator map; its generated `k`-algebra is precisely the image of `k`. The nonempty case is the stated theorem.

### [`P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.MapsDvdSol.opFamily_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.lean#L343-L365) — `flt-anthropic-0134`

Snippet: `samples/flt-anthropic/flt-anthropic-0134.lean`

- `[IsDomain 𝒪]` (variable): The conclusion and proof need only `[CommRing 𝒪]`. The source theorem `P2MW.S_CohCarrier_opFamily_comm.solution` proves the same commutation statement under `[CommRing 𝒪]` and `[NeZero L]`; it does not require that 𝒪 be a domain. Removing this instance leaves the statement well-typed and the proof can use that result.
- `[CharZero 𝒪]` (variable): The conclusion and proof need only `[CommRing 𝒪]`. The source theorem `P2MW.S_CohCarrier_opFamily_comm.solution` proves the same commutation statement under `[CommRing 𝒪]` and `[NeZero L]`, without a characteristic-zero assumption. Removing this instance leaves the statement well-typed and the proof can use that result.
- `[IsLocalRing 𝒪]` (variable): The conclusion and proof need only `[CommRing 𝒪]`. The source theorem `P2MW.S_CohCarrier_opFamily_comm.solution` proves the same commutation statement under `[CommRing 𝒪]` and `[NeZero L]`, without a local-ring assumption. Removing this instance leaves the statement well-typed and the proof can use that result.

### [`P2MW.S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.ModularCurve.map_eval₂_aeval_toRingHom`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_monic_natDegree_le_aeval_jqModC_eq_zero.lean#L18-L24) — `flt-anthropic-0137`

Snippet: `samples/flt-anthropic/flt-anthropic-0137.lean`

- `[Algebra ℤ A]` (theorem): The preceding `[CommRing A]` supplies `[Ring A]`, from which Mathlib provides `Ring.toIntAlgebra : Algebra ℤ A` (Mathlib/Algebra/Algebra/Basic.lean:296). Thus this instance can be deleted and inferred instead; the resulting statement and proof remain valid, including for the zero ring.
- `[Algebra ℤ B]` (theorem): The preceding `[CommRing B]` supplies `[Ring B]`, from which Mathlib provides `Ring.toIntAlgebra : Algebra ℤ B` (Mathlib/Algebra/Algebra/Basic.lean:296). Thus this instance can be deleted and inferred instead; the resulting statement and proof remain valid, including for the zero ring.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.C2Count.natCard_finPts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.lean#L214-L257) — `flt-anthropic-0143`

Snippet: `samples/flt-anthropic/flt-anthropic-0143.lean`

- `(hm : 0 < m)` (theorem): The coprimality hypothesis already implies m ≠ 0: `not_dvd_of_coprime hmp` gives `¬ p ∣ m`, whereas m = 0 would imply p ∣ m. Hence m > 0. The proof can derive `hm` locally from `hmp` and use it where needed, including in the surjectivity and injectivity arguments. The conclusion has no other dependence on `hm`; the m = 0 case is excluded by `hmp`.

### [`P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.AlgebraicCurve.BaseChangeTwo.lhs_eq_rhs_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_add_of_normFormulaAlong.lean#L327-L359) — `flt-anthropic-0149`

Snippet: `samples/flt-anthropic/flt-anthropic-0149.lean`

- `(hg : g ≠ 0)` (theorem): If g = 0, `Place.ord_zero` (in `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`) and hD give D v = 0 for every place v, hence D = 0 by extensionality of `Divisor`. Both lhs and rhs are additive homomorphisms, so they send 0 to 0. Thus the conclusion holds in this case too; the existing proof applies when g ≠ 0.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.P2mFlatIsog.ringKrullDim_stalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.lean#L246-L300) — `flt-anthropic-0150`

Snippet: `samples/flt-anthropic/flt-anthropic-0150.lean`

- `[IsIntegral Y]` (theorem): It can be removed: on the chosen nonempty affine open V, put B = Γ(Y,V) and A = Γ(X,h ⁻¹ᵁ V). Since h is finite, B → A is finite; since h is surjective and A is a domain by [IsIntegral X], its kernel is the nilradical of B. Thus B_red embeds integrally into A, and both are finite type algebras over K. Replace the comparison with height_comap_eq for B_red → A; localization at the corresponding primes gives the same stalk dimensions, since quotienting by nilpotents does not change prime spectra or Krull dimensions. This also covers nonreduced Y, including the zero-dimensional case.

### [`P2MW.S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.FLT.NumberTheory.kw_hjoint_normBasis_liftHom_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuadraticForm_forall_exists_ternary_pureNrd_eq_of_exists_ne_zero_eq_zero.lean#L674-L685) — `flt-anthropic-0151`

Snippet: `samples/flt-anthropic/flt-anthropic-0151.lean`

- `[CharZero F]` (variable): The conclusion's types and formula need `[Field F]`, but not characteristic zero: `kw_hjoint_normBasis` is defined by the displayed matrices and polynomial basis identities, and the application proof uses only matrix algebra and `ring`. Those identities remain valid in every characteristic, including characteristic two; no division or cancellation by a nonzero numeral is involved. Thus the `CharZero` instance can be omitted while keeping the statement and proving it by the same calculation.

### [`P2MW.S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.K51A1.retr_tmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isClosedEmbedding_unitsMap_includeRight.lean#L38-L40) — `flt-anthropic-0160`

Snippet: `samples/flt-anthropic/flt-anthropic-0160.lean`

- `[FiniteDimensional K L]` (variable): The theorem’s statement and the definition of `retr` do not require finite dimensionality. The proof uses only `LinearMap.rTensor_tmul` and `TensorProduct.lid_tmul`, so it works unchanged without this instance.
- `[IsTopologicalRing A]` (variable): The theorem’s statement and proof do not use the topological ring structure; `retr` is defined and the displayed tensor identities hold without it. This instance can be deleted while retaining `[TopologicalSpace A]`. (The topology instance itself remains needed to form the retained `IsTopologicalRing A` binder’s type.)

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.R4ODGlue.eq_of_proj_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.lean#L415-L421) — `flt-anthropic-0167`

Snippet: `samples/flt-anthropic/flt-anthropic-0167.lean`

- `hcomm` (variable): The equality follows from `hpb` alone. Apply `hpb` to `(0 : A')` and `(0 : A'')`; they are compatible since both map to zero. Its uniqueness says the only element of `B` whose two projections are zero is zero. Since `h'` and `h''` imply that `b₁ - b₂` has both projections zero, it must be zero, hence `b₁ = b₂`. This also works in degenerate rings; `hcomm` is not needed.

### [`P2MW.S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.KcSemiLocalIwasawaHaar.coe_nGL`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_pos_forall_integrable_and_twistedWeighted_add_mul_twistedOrbital_eq_mul_integral_iwasawa_of_normString_diagUnits2_eq.lean#L1038-L1038) — `flt-anthropic-0168`

Snippet: `samples/flt-anthropic/flt-anthropic-0168.lean`

- `[NumberField L]` (variable): The statement and proof only use L as a field in the tensor product E; no number-field property of L is needed. With [Field L] retained, E and the matrix types still elaborate. The identity follows directly from the defining matrix formula for AutomorphicForm.unipotentGL2 (the proof here is rfl), so it remains true without [NumberField L].

### [`P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq.DS575Sol.Fbar_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq.lean#L142-L145) — `flt-anthropic-0171`

Snippet: `samples/flt-anthropic/flt-anthropic-0171.lean`

- `[NeZero N]` (variable): The statement's types and quotient are defined without [NeZero N], and the proof uses only Fbar_mk and slashV_add; neither requires it. Gamma_normal, used in defining slashV, also has no nonzero assumption. Thus the same proof works for N = 0 as well as other N, without changing the statement.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.AlgebraicCurve.AlgebraicCurve.adeleBddPrincipal_eq_comap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean#L791-L793) — `flt-anthropic-0183`

Snippet: `samples/flt-anthropic/flt-anthropic-0183.lean`

- `[HasPrincipalDivisors K F]` (theorem): The equality follows from the definition of `adeleBddPrincipal` without requiring `globalSub K F ≤ adeleSpace K F`. For the reverse inclusion, if an element of `adeleSpace` lies in `adeleBdd D ⊔ globalSub K F`, write it as a sum of elements from those two submodules. The `adeleBdd D` summand is in `adeleSpace` by `adeleBdd_le_adeleSpace`, so subtracting it shows the `globalSub` summand is also in `adeleSpace`. This gives membership in the supremum of the two comaps; the other inclusion is immediate. This argument also covers zero and needs no condition on the field elements' divisors.

### [`P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE.ell_sub_eq_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.lean#L175-L187) — `flt-anthropic-0184`

Snippet: `samples/flt-anthropic/flt-anthropic-0184.lean`

- `(hf0 : f ≠ 0)` (theorem): If f = 0, `Place.ord_zero` makes hP say P v = 0 for every place, so P = 0 as a Finsupp divisor. Then E - P = E and the conclusion holds directly. If f ≠ 0, the existing multiplication-by-f linear equivalence proof applies. Thus the theorem can split on f = 0 and does not need hf0 as a hypothesis.

### [`P2MW.S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.AlgebraicGeometry.OModulePresheaf.Rebase.e0_smulB`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage.lean#L392-L398) — `flt-anthropic-0192`

Snippet: `samples/flt-anthropic/flt-anthropic-0192.lean`

- `[IsSeparated q]` (variable): This section variable is not needed by the statement or proof. The statement's definitions (`GW`, `e0`, and the cochain types) do not require separatedness, and the proof uses only `G.res_smul` and `Scheme.Hom.appLE_map`; the former is part of the OModulePresheaf structure without a separatedness assumption. Thus the same equality is provable for any `q`, including degenerate cases.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.eq_span_tInvChart_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L2727-L2734) — `flt-anthropic-0199`

Snippet: `samples/flt-anthropic/flt-anthropic-0199.lean`

- `(ht : Transcendental κ t)` (variable): With `hchartInv`, the chart ring is generated over κ by `t⁻¹`. If `t` is algebraic, this generated domain is a field, so its only prime ideals are ⊥ and ⊤; the ideal generated by `tInvChart` is respectively ⊥ if `t⁻¹ = 0`, or ⊤ otherwise. Thus any prime containing `tInvChart` equals its span. This includes the zero case. If `t` is transcendental, the existing proof via `eq_span_of_pow_mem` applies, since `transcendental_inv` gives transcendence of `t⁻¹`. Hence the conclusion remains provable without `ht`, by splitting on whether `t` is algebraic.

### [`P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.HeckeGammaH.sum_slash_beta_eq_heckeU_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean#L381-L463) — `flt-anthropic-0201`

Snippet: `samples/flt-anthropic/flt-anthropic-0201.lean`

- `(B : BezoutData M ℓ)` (theorem): `B` appears nowhere in the statement except in its own binder type. It is only used by the proof to choose representatives. From `ρ : Gamma0 M`, the determinant condition and the lower-left divisibility imply that the reduction of the `(1,1)` entry of `ρ` is a unit modulo `M`. By `hρ`, that reduction is `ℓ`, so `¬ ℓ ∣ M`. The source already provides `exists_bezoutData`, which gives a `BezoutData M ℓ` from this fact and the prime hypothesis. Thus, after deleting `B`, the proof can choose such a datum internally and proceed unchanged; the degenerate case `M = 0` is excluded by `[NeZero M]`.

### [`P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.RoadA.coe_τ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.lean#L325-L326) — `flt-anthropic-0219`

Snippet: `samples/flt-anthropic/flt-anthropic-0219.lean`

- `[NeZero M]` (variable): The statement uses `M` only through `modularFunctionFieldBar M` and `τ M σ`; these are defined using `modularFunctionFieldFull M` and `arithmeticRingAut`, neither of which requires `[NeZero M]`. The `rfl` proof still works with `M = 0`: the field constructions are defined for every natural number, including zero. Thus the theorem remains provable after omitting this instance.

### [`P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc.Bdd.mul_small`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PowerSeries_dvd_of_forall_taylorShift_order_le.lean#L132-L135) — `flt-anthropic-0231`

Snippet: `samples/flt-anthropic/flt-anthropic-0231.lean`

- `(hC : 0 ≤ C)` (theorem): This follows from hP: at coefficient 0, 0 ≤ ‖coeff 0 P‖ ≤ C. Thus the proof can supply this nonnegativity without hC; no degenerate case is excluded.
- `(hC' : 0 ≤ C')` (theorem): From hQ at k = m, 0 ≤ ‖coeff m Q‖ ≤ C' * ρ ^ 0 = C'. Thus hQ itself implies C' ≥ 0, so this hypothesis can be omitted when applying the multiplication estimate.

### [`P2MW.S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.SupersingularTop3.mem_of_ord_nonneg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.lean#L40-L46) — `flt-anthropic-0240`

Snippet: `samples/flt-anthropic/flt-anthropic-0240.lean`

- `(hf : f ≠ 0)` (theorem): The case `f = 0` is covered: `Place.ord_zero` gives `w.ord 0 = 0`, so the order condition holds, and `0` belongs to `w.toValuationSubring`. Split on whether `f = 0`; in the nonzero case, the existing proof applies. Thus `hf` can be deleted.

### [`P2MW.S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.lean#L16-L30) — `flt-anthropic-0249`

Snippet: `samples/flt-anthropic/flt-anthropic-0249.lean`

- `[DecidableEq F]` (theorem): The statement only uses the field operations, the affine-point group structure, `coordsOrZero`, and the polynomial predicate `IsTwoKernel`; none require decidable equality on `F`. In particular, `coordsOrZero` is defined by point constructors, `IsTwoKernel` is stated using polynomial degree/coefficient/divisibility, and `addOrderOf` is defined without a `DecidableEq` assumption. Removing this binder leaves the statement meaningful, and the proof steps do not use it (the `if_neg` concerns the coefficient index `1`, not `F`).

### [`P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.R4RRN.FF_slash_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0.lean#L366-L368) — `flt-anthropic-0250`

Snippet: `samples/flt-anthropic/flt-anthropic-0250.lean`

- `[NeZero M']` (variable): The theorem's proof is an algebraic slash-action calculation using `slash_conjElem_eq_FF` and cancellation of `Dr q`; it does not use `NeZero M'`. The type `ModularForm (Γ q M') k` still makes sense without this instance: `Γ q M'` is defined from the congruence subgroup `GH q M'` without requiring `M' ≠ 0`. Thus deleting the section variable `[NeZero M']` leaves the statement and proof valid, including when `M' = 0`.

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.QMHecke12.exists_generator`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.lean#L368-L422) — `flt-anthropic-0252`

Snippet: `samples/flt-anthropic/flt-anthropic-0252.lean`

- `(hι : Function.Injective ι)` (variable): The injectivity assumption can be deleted: `hB` yields `a ≠ 0` and `b ≠ 0`, and `QMPeriodLatticeFull.injective_of_ne_zero` proves that every such algebra homomorphism `ι` is injective. The proof already obtains the required injectivity via `qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span`, without using `hι`.

### [`P2MW.S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.AlgebraicCurve.AlgebraicCurve.Place.stichtenothGenusExists_of_isFractionRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean#L2159-L2166) — `flt-anthropic-0261`

Snippet: `samples/flt-anthropic/flt-anthropic-0261.lean`

- `[Algebra.IsSeparable E F]` (variable): The conclusion and the construction of the pole-divisor package do not require separability. The proof can be rebuilt through the same steps without it: `FiniteDimensional.exists_is_basis_integral` (Mathlib's `RingTheory/DedekindDomain/IntegralClosure.lean`) only requires the finite-dimensional extension and the fraction-ring setup; the remaining regular-outside and package construction uses the tower data and finite-dimensionality, not separability. Thus this instance can be removed while keeping the other hypotheses, including `[FiniteDimensional E F]`.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.WeierstrassCurve.WeierstrassCurve.ModularCurve.kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean#L3405-L3408) — `flt-anthropic-0263`

Snippet: `samples/flt-anthropic/flt-anthropic-0263.lean`

- `[DecidableEq F]` (variable): The conclusion uses F as a field but does not require decidable equality. The proof is just `Transcendental.of_tower_top` applied to the transcendence result over F'; neither that step nor `transcendental_polyToFunctionField_X` requires `[DecidableEq F]`.
- `[CharZero F]` (variable): The conclusion and proof do not require characteristic zero on F. The tower argument and the cited transcendence result work without this assumption.
- `[DecidableEq F']` (variable): The conclusion and the proof's use of `transcendental_polyToFunctionField_X` do not require decidable equality on F'. The result still follows by the same tower argument without this instance.
- `[CharZero F']` (variable): The proof only needs the transcendence result over F' and then `Transcendental.of_tower_top`; neither requires characteristic zero on F'. The statement remains true without this assumption.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F).toAffine]` (variable): This instance concerns the base change to F, whereas the proof uses only the transcendence result for the base change to F' and the field tower. It can be omitted without affecting the statement or proof.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]` (variable): This instance concerns the base change to F and is not needed: the proof uses only the transcendence result for the base change to F' and the field tower.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]` (variable): This assumption concerns the base change to F and is not used by the proof, which only invokes the transcendence result for the base change to F' and the field tower.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F').toAffine]` (variable): The cited `transcendental_polyToFunctionField_X` result for an affine curve does not require a GenusOnePlaceGate instance. The proof and conclusion therefore remain valid without this assumption.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]` (variable): The cited `transcendental_polyToFunctionField_X` result for an affine curve does not require a centred gate instance; the proof only needs that result and the field tower.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]` (variable): The cited `transcendental_polyToFunctionField_X` result for an affine curve does not require an AbelTheorem instance. It can be removed while retaining the same proof.

### [`P2MW.S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.lean#L203-L596) — `flt-anthropic-0267`

Snippet: `samples/flt-anthropic/flt-anthropic-0267.lean`

- `(hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)` (theorem): This follows from the other hypotheses: for prime q dividing N, if q = p then hpSmin and hSmin give q ∈ S; otherwise hN.2 gives q ∈ Smin, and hSmin gives q ∈ S. A proof can derive hNS this way and use the derived fact wherever the current proof passes hNS. The binder is not needed to elaborate the remaining statement.

### [`P2MW.S_Function_orbitCensus_of_dihedralThree_relations.P2MKcOrbitCensus.b_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean#L14-L17) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- `[Fintype X]` (variable): This instance is not needed by `Function.Injective b` or the proof: applying `b ∘ b` to `b x = b y` and using `hb` gives `x = y`. The argument works for empty and trivial types as well.
- `[DecidableEq X]` (variable): This instance is not needed by `Function.Injective b` or the proof: applying `b ∘ b` to `b x = b y` and using `hb` gives `x = y`. The argument works for empty and trivial types as well.

### [`P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.KcHaarQuotientMulRight.lintegral_density_mul_comp_mul_right_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.lean#L75-L109) — `flt-anthropic-0270`

Snippet: `samples/flt-anthropic/flt-anthropic-0270.lean`

- `[SFinite μH]` (theorem): This follows from the other assumptions. The closedness proof gives `SigmaCompactSpace H` via `IsClosed.sigmaCompactSpace`; `[μH.IsHaarMeasure]` provides finiteness on compact sets. Mathlib's `SigmaFinite.of_isFiniteMeasureOnCompacts` then gives `SigmaFinite μH`, which yields `SFinite μH`. Thus the theorem can be proved without taking `[SFinite μH]` as an argument.

### [`P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.UqNSol.fstDiv_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean#L358-L366) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- `[hqN : Fact (¬ q ∣ N)]` (variable): `hqN` is automatically included because it is instance-implicit and its parameters `q` and `N` occur in the theorem’s arguments, but it is not needed by the statement or proof. The `PlaceSpecialization` type takes no such hypothesis. The proof can be given without it by unfolding `fstDiv` and applying `Finsupp.filter_add` in the inductive step, as in `fstDiv_add`; the empty case uses `Finsupp.filter_zero`. This argument also covers empty sums and does not rely on any condition on `q` or `N`.

### [`P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.LCMazur.OrdQ.span_singleton_eq_range_ordProj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.lean#L263-L272) — `flt-anthropic-0275`

Snippet: `samples/flt-anthropic/flt-anthropic-0275.lean`

- `(h2 : finrank A V = 2)` (theorem): The factorization `hφ` already forces the rank to be 2: under the local-ring assumptions, `A` is nontrivial and has `StrongRankCondition`, so Mathlib's `LinearMap.charpoly_natDegree` identifies the characteristic polynomial's natural degree with `finrank A V`. The right-hand side of `hφ` is a monic quadratic, hence has natural degree 2. Thus one can derive `h2` from `hφ` and use it in the existing proof. The factorization and this degree argument also handle the degenerate cases; no zero-eigenvalue or equal-eigenvalue exception is needed.

### [`P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.lean#L27-L40) — `flt-anthropic-0278`

Snippet: `samples/flt-anthropic/flt-anthropic-0278.lean`

- `(ha : a ≠ 0)` (theorem): The excluded case is true: if a = 0, then μ 0 = 0 by AbsoluteValue.map_zero, so μ 0 < 1, and the subtype ⟨0, haA⟩ is zero, which belongs to the maximal ideal. For a ≠ 0, the existing proof applies unchanged. Thus the theorem can be proved by splitting on a = 0.

### [`P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.TH1Wanted2.inv_mem_and_const_mem_of_gaussPresentation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.lean#L874-L964) — `flt-anthropic-0285`

Snippet: `samples/flt-anthropic/flt-anthropic-0285.lean`

- `(hq3 : q = 3)` (theorem): The proof never uses `hq3`, and the rest of the statement does not depend on it. Deleting it leaves the statement unchanged; the existing proof goes through without it.
- `(hqM' : ¬ q ∣ M')` (theorem): The proof never uses `hqM'`, and the rest of the statement does not depend on it. Deleting it leaves the statement unchanged; the existing proof goes through without it.

### [`P2MW.S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.P2mConormLSpace.CFE.trace_algebraMap'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.lean#L193-L203) — `flt-anthropic-0287`

Snippet: `samples/flt-anthropic/flt-anthropic-0287.lean`

- `[Algebra.IsSeparable K K']` (variable): The condition `hconst` says every element of `F` algebraic over `K` lies in the image of `K`, so `F/K` is regular. A regular extension is linearly disjoint from algebraic extensions of `K`, including `K'`, whether or not `K'/K` is separable. Since `hgen` says `F'` is generated over `F` by the image of `K'`, the trace identity follows from the linearly-disjoint trace formula `LinearDisjoint.trace_algebraMap` (Mathlib’s `FieldTheory/LinearDisjoint.lean`). The other hypotheses ensure the extensions and traces in the statement are defined; no zero, trivial-field, or empty case causes an exception.

### [`P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.WNormSwapSol.θ_θ_γel`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.lean#L941-L962) — `flt-anthropic-0295`

Snippet: `samples/flt-anthropic/flt-anthropic-0295.lean`

- `(hζ : IsPrimitiveRoot ζ p)` (variable): The conclusion does not mention ζ. Without this argument, the proof can choose a primitive pth root in Qb = AlgebraicClosure ℚ: Mathlib provides HasEnoughRootsOfUnity (AlgebraicClosure F) n when n is nonzero in F, and p is nonzero in ℚ since p is prime. Use that chosen root and its primitive-root proof in map_μ_eq and the subsequent proof; the coefficient argument still works because the chosen ζ is a unit. The other included hypotheses remain available for θ_θ_incl.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.AlgebraicCurve.DiscRigidity.sum_filter_eq_of_degreeOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.lean#L80-L105) — `flt-anthropic-0299`

Snippet: `samples/flt-anthropic/flt-anthropic-0299.lean`

- `(hf : f ≠ 0)` (theorem): If f = 0, `Place.ord_zero` gives `v.ord f = 0` for every v. Then hDf makes every summand Df v zero, so both finite sums are zero, regardless of D and D'. For f ≠ 0, the existing proof applies. Thus hf can be removed by splitting on whether f is zero.


## Formal Frontier (15 flagged)

### [`GradedRing.Veronese.adjoin_component_one_eq_top`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseDegreeOne.lean#L80-L104) — `formal-frontier-0005`

Snippet: `samples/formal-frontier/formal-frontier-0005.lean`

- `(hn : 0 < n)` (theorem): The conclusion also holds for n = 0. Then every selected component 𝒮 (0 * j) is 𝒮 0, and each pure summand DirectSum.of j s is generated over component 𝒮 0 0 by component 𝒮 0 1: for j = 0 it lies in the coefficient subalgebra, and for j > 0 it is the product of the degree-one summand with coefficient s and j−1 degree-one summands with coefficient 1. DirectSum induction then gives the result. For n > 0 the existing proof applies. The hgen hypothesis remains necessary in general, since a ring with a nonzero component in degree 2 and zero component in degree 1 need not be generated by its degree-zero and degree-one components.

### [`CategoryTheory.splitKernelProductIso_mul_lift`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupObject/SplitKernelSemidirect.lean#L115-L126) — `formal-frontier-0072`

Snippet: `samples/formal-frontier/formal-frontier-0072.lean`

- `[IsMonHom i]` (variable): The statement and proof need i only as a morphism: splitKernelConj and splitKernelProductIso do not require i to preserve multiplication. The group calculation can be proved using splitKernelConj_lift_comp_i, whose statement and proof require neither [IsMonHom i] nor [IsMonHom e], followed by the group laws. The argument remains valid in degenerate cases since it uses only the stated group-object laws and pullback property.
- `[IsMonHom e]` (variable): The product isomorphism and restricted conjugation are defined for an arbitrary section e satisfying he; neither requires e to preserve multiplication. The proof's conjugation readback splitKernelConj_lift_comp_i holds without [IsMonHom e], so the remaining equality follows from group laws on the morphisms. No degenerate case requires multiplicativity of e.

### [`Nat.DivisionGrowth.affine_lower_bound`](https://github.com/FormalFrontier/sequence-growth/blob/7b7db3df8a043a09d037de4ff1eced6873404fb2/SequenceGrowth/Data/Nat/DivisionGrowth.lean#L68-L94) — `formal-frontier-0117`

Snippet: `samples/formal-frontier/formal-frontier-0117.lean`

- `(hs : 0 < s)` (theorem): The theorem remains true when s = 0: then s - 1 = 0 and rational division by s is division by zero, which is 0, so the left side is u 0 when m = 0 and 0 when m > 0. Both are at most u m. When s ≠ 0, hs follows from s being a natural number, and the existing proof through affine_step applies. Thus hs can be removed by splitting on s = 0; hsn ensures the denominator n - s is positive in the zero case.

### [`ContinuousGroupCohomology.LevelCompact.finiteTateNegative_eq_positiveHomology`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/CompactNegativeTate.lean#L372-L381) — `formal-frontier-0134`

Snippet: `samples/formal-frontier/formal-frontier-0134.lean`

- `[IsTopologicalGroup G]` (variable): The statement and the definitions it uses need only `[Group G]` and `[TopologicalSpace G]` on the ambient group. In particular, `LevelCompact` is defined without an ambient topological-group assumption, and `continuous_quotientToInvariants_action` has only those weaker ambient assumptions. The definitional equality remains `rfl` without this instance.
- `[CompactSpace G]` (variable): Compactness of the ambient group is not used: `LevelCompact` supplies compactness for the coefficient invariants, and the finite-bar construction uses the finite quotient and those coefficient topologies. The statement and its `rfl` proof therefore remain valid without `[CompactSpace G]`.

### [`IsKrasner.adjoin_rootSet_le_adjoin_rootSet_of_norm_coeff_sub_lt`](https://github.com/FormalFrontier/polynomial-root-stability/blob/ceae7822f6151ec6626678db1653054d3398cff3/PolynomialRootStability/Krasner.lean#L363-L391) — `formal-frontier-0152`

Snippet: `samples/formal-frontier/formal-frontier-0152.lean`

- `(hε : 0 < ε)` (theorem): This follows from the other hypotheses: take `i = f.natDegree` in `hcoeff`. By `hdeg` and `Monic.coeff_natDegree` for `hfm` and `hgm`, both coefficients are 1, so `hcoeff` gives `‖1 - 1‖ < ε`, hence `0 < ε`. This also works in degree zero. The proof can derive `hε` this way and pass it to `exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`; no degenerate case is excluded.

### [`Subgroup.exists_continuous_coset_representative`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ContinuousCosetRepresentative.lean#L55-L74) — `formal-frontier-0160`

Snippet: `samples/formal-frontier/formal-frontier-0160.lean`

- `[T2Space G]` (variable): Totally disconnectedness implies that any preconnected subset, in particular the pair consisting of 1 and a point in the closure of {1}, is a subsingleton. Thus {1} is closed. By Mathlib’s `IsTopologicalGroup.t2Space_iff_one_closed`, this yields `T2Space G`; the proof can then proceed with that derived instance. This also covers the trivial group.

### [`MvPowerSeries.isUnit_adicallyRestricted_iff_coeff_radical`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean#L83-L92) — `formal-frontier-0162`

Snippet: `samples/formal-frontier/formal-frontier-0162.lean`

- `[IsAdicComplete I R]` (variable): Completeness can be dropped because the right-hand side already requires the constant coefficient to be a unit. The formal power series then has an inverse. For each k, the restriction condition makes f modulo I^k a polynomial; its nonconstant coefficients are nilpotent modulo I^k, and there are only finitely many of them. Thus its nonconstant part is nilpotent, so this polynomial is a unit and its polynomial inverse agrees with the reduction of the formal inverse. That shows the inverse is adically restricted. Conversely, a restricted unit reduces modulo I to a unit polynomial, whose nonconstant coefficients are nilpotent, giving the stated radical condition; its constant coefficient is a unit. These arguments do not require IsAdicComplete.

### [`FundamentalGroup.existsUnique_hom_of_isOpenCover`](https://github.com/FormalFrontier/fundamental-groupoids/blob/2fdb99858e3feb7a6a06ae10915f286364de2cc1/FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean#L404-L527) — `formal-frontier-0164`

Snippet: `samples/formal-frontier/formal-frontier-0164.lean`

- `(hU : IsPathConnected (U : Set X))` (theorem): This can be deleted on its own: only the path component of p in U matters to the based fundamental group. Since hI makes the entire overlap path connected and it contains p, every component of U that meets V is the component of p; any other U-components are disjoint from V and do not affect based loops in X. The descent proof can therefore use paths and frames on the components relevant to p, without requiring all of U to be path connected. The point p still supplies a nonempty relevant component.
- `(hV : IsPathConnected (V : Set X))` (theorem): Symmetrically, this can be deleted on its own: every component of V meeting U is the component of p, by path connectedness of the overlap, and components disjoint from U do not affect based loops in X. Restricting the descent argument to the components relevant to p gives the same extension and uniqueness. The point p ensures the relevant component is nonempty.

### [`GradedRing.Veronese.finiteType_of_finiteType`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseFiniteType.lean#L105-L126) — `formal-frontier-0179`

Snippet: `samples/formal-frontier/formal-frontier-0179.lean`

- `(hn : 0 < n)` (theorem): The conclusion also holds at n = 0: `GradedRing.Veronese.finiteType_zero` proves it without a finite-type assumption. With hn retained, the existing proof handles n > 0. Thus after deleting hn, split on n = 0 versus 0 < n and use `finiteType_zero` in the zero case and the existing theorem in the positive case.

### [`AlgebraicGeometry.Proj.degreeScaledChartMap_preimage_basicOpen`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/DegreeScaledMap.lean#L453-L469) — `formal-frontier-0188`

Snippet: `samples/formal-frontier/formal-frontier-0188.lean`

- `(hr : r ∈ 𝒜 n)` (theorem): The equality holds for arbitrary r: basicOpen of an arbitrary element is the union of the basic opens of its homogeneous components, and the degree-scaled graded map carries those components to the corresponding components of f r. The chart preimage identity therefore extends componentwise; the proof need not use hr. This also covers r = 0 or 1 and the empty-Proj case.
- `(hn : 0 < n)` (theorem): For homogeneous r, the chart-preimage equality also holds in degree zero: the localization map sends the degree-zero element represented by r to the one represented by f r, so their basic opens have the same preimage. Thus the positive-degree restriction used by the cited auxiliary lemma is a proof limitation, not needed for the statement; the degree-zero and trivial/empty cases cause no exception.

### [`finiteGroupPresentation_iff_compact_totallyDisconnected`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/FiniteGroupCharacterization.lean#L198-L214) — `formal-frontier-0200`

Snippet: `samples/formal-frontier/formal-frontier-0200.lean`

- `[T2Space G]` (theorem): This can be deleted: a totally disconnected topological group is Hausdorff. Indeed, total disconnectedness makes the closure of each singleton a preconnected subsingleton, so singletons are closed; then `IsTopologicalGroup.t2Space_iff_one_closed` gives `T2Space G`. Thus the reverse direction can derive the instance needed for `ProfiniteGrp.of G`. In the forward direction, the presentation already gives a homeomorphism to a limit of profinite groups, hence compactness and total disconnectedness without assuming Hausdorffness of G. The argument also covers the trivial group.

### [`DirectLimit.VaryingScalar.fromTensorLimit_mk`](https://github.com/FormalFrontier/algebraic-direct-limits/blob/1bf0740b01951905e0ba12bd5d2bdb67819c12d1/AlgebraicDirectLimits/VaryingScalar.lean#L389-L392) — `formal-frontier-0210`

Snippet: `samples/formal-frontier/formal-frontier-0210.lean`

- `[Nonempty ι]` (variable): The theorem’s statement and its `rfl` proof do not need a chosen index: the direct-limit types and maps in the statement are well-typed without `[Nonempty ι]`. Removing this instance leaves the theorem universally quantified over `i : ι`; if `ι` is empty, there is no such `i`, so the claim is vacuous. The other order assumptions and algebraic instances remain available.

### [`AlgebraicGeometry.Scheme.Hom.ker_radical_of_isReduced_source`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L154-L160) — `formal-frontier-0232`

Snippet: `samples/formal-frontier/formal-frontier-0232.lean`

- `[QuasiCompact f]` (theorem): The definition of `f.ker` does not require quasi-compactness; it is the largest ideal sheaf below the family of componentwise ring-map kernels (`Hom.ker` and `ofIdeals` in `IdealSheaf/Basic.lean`). Quasi-compactness is only used by `ker_apply` to identify those ideals with the componentwise kernels. Without it, `f.ker` still lies below that family, whose ideals are radical because the target section rings over the reduced source are reduced (`Ideal.isRadical_bot.comap`). Thus `f.ker.radical` also lies below the family, so maximality gives `f.ker.radical ≤ f.ker`; the reverse inclusion always holds. This proves the same statement without `[QuasiCompact f]`.

### [`CountableEndomorphism.free_kernel`](https://github.com/FormalFrontier/stable-range/blob/c283b01ed9ebc33c7eefcdb4f3d2ca45141f469e/StableRange/CountableEndomorphism.lean#L251-L262) — `formal-frontier-0257`

Snippet: `samples/formal-frontier/formal-frontier-0257.lean`

- `[AddCommGroup M]` (variable): The statement still makes sense for an `AddCommMonoid` module: the Finsupp parity splitting and the endomorphism semiring do not require additive inverses. The kernel is directly isomorphic, as a module over the opposite endomorphism semiring, to one copy of `Module.End S (ℕ →₀ M)`: send a kernel element `k` to `y₁ * k`, with inverse `r ↦ x₁ * r`. The parity decomposition identity `x₀ * y₀ + x₁ * y₁ = 1` shows these maps are inverse on the kernel, since `y₀ * k = 0`. The endomorphism semiring is free over itself, so freeness follows without the group hypothesis; this direct argument replaces the current proof’s ring-based rectangular-inverse criterion. The trivial-module case is included: both the kernel and coefficient semiring are trivial.

### [`MvPowerSeries.existsUnique_firstVariable_division_of_scalar_top`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableDivision.lean#L112-L132) — `formal-frontier-0285`

Snippet: `samples/formal-frontier/formal-frontier-0285.lean`

- `(hc : c ≠ 0)` (theorem): It follows from the other hypotheses, including when d = 0. Let p be `MvPolynomial.finSuccEquiv _ n (restrictedResidue a ham f)`. If p were zero, every coefficient of f would lie in the maximal ideal, by the coefficient formula for `restrictedResidue` and the kernel of the quotient map. Then the ideal generated by those coefficients would lie in the maximal ideal, contradicting `hprim` since the maximal ideal is proper. Thus p ≠ 0. For a nonzero polynomial, its coefficient at its natDegree is nonzero, so `hdegree` gives `p.coeff d ≠ 0`. By `htop`, this coefficient is `MvPolynomial.C c`, hence c ≠ 0. The proof can derive `hc` this way and pass it to the existing leading-exponent lemma; this also handles degree zero.

