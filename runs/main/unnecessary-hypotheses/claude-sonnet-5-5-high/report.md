# unnecessary-hypotheses: run `main`, judge `claude-sonnet-5-5-high`

| Library | Sampled | Judged | Flagged | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|
| Mathlib | 1000 | 300 | 6 | 2.0% | 0.9%–4.3% | $5.45 |
| Tau Ceti | 1000 | 300 | 12 | 4.0% | 2.3%–6.9% | $11.26 |
| Lean Pool | 1000 | 300 | 39 | 13.0% | 9.7%–17.3% | $10.27 |
| FLT (Anthropic) | 1000 | 300 | 52 | 17.3% | 13.5%–22.0% | $14.93 |
| Formal Frontier | 1000 | 300 | 12 | 4.0% | 2.3%–6.9% | $10.30 |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (6 flagged)

### [`RatFunc.Luroth.Φ_natDegree_eq_φ_natDegree`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/RatFunc/Luroth.lean#L182-L185) — `mathlib-0077`

Snippet: `samples/mathlib/mathlib-0077.lean`

- `(h : E ≠ ⊥)` (theorem): The statement is still true when E = ⊥. Then X is transcendental over K, and K → ⊥ is bijective, so X is transcendental over E. So `minpoly E X = 0`, i.e. `φ E = 0`, and `(φ E).natDegree = 0`. Next, `Φ' E` is `integerNormalization _ (map 0) = integerNormalization _ 0`, which is 0 by `IsFractionRing.integerNormalization_eq_zero_iff`. Then `Φ E = (0 : K[X][Y]).primPart = 1` by `Polynomial.primPart_zero` (primPart is defined as `if p = 0 then 1 else ...`). So `(Φ E).natDegree = natDegree 1 = 0`, and both sides are 0. The proof is `by_cases h : E = ⊥`. The ≠ ⊥ case is the existing proof. In the = ⊥ case, show `φ E = 0` using `minpoly.eq_zero` applied to non-integrality of X over E (from transcendence of X over K, via `IsAlgebraic.restrictScalars` or similar, since E = ⊥ is the image of K), then `simp [primPart_zero]`.

### [`Module.Basis.toMatrix_mulVec_repr`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Matrix/Basis.lean#L231-L236) — `mathlib-0083`

Snippet: `samples/mathlib/mathlib-0083.lean`

- `[Finite ι']` (theorem): The statement does not need `Finite ι'` to elaborate. `Basis.toMatrix e v` is defined as `fun i j ↦ e.repr (v j) i` with no finiteness assumption. `b'.toMatrix b : Matrix ι' ι R` and `*ᵥ` only sums over the column index `ι`, which is covered by the variable `[Fintype ι]`. The statement is still true for infinite `ι'`. Since `ι` is a Fintype, `m = ∑ j, b.repr m j • b j` (`Basis.sum_repr`). Applying the linear map `b'.repr` and evaluating at `i : ι'` gives `b'.repr m i = ∑ j, b.repr m j * b'.repr (b j) i`. By `Basis.toMatrix_apply`, `b'.toMatrix b i j = b'.repr (b j) i`, so this is the `i`-th entry of `b'.toMatrix b *ᵥ b.repr m`. The proof can be a pointwise `ext i` computation along these lines. The `Finite ι'` is only used in the current proof to go through `LinearMap.toMatrix`, which needs a Fintype on `ι'`. Degenerate cases such as empty `ι'` or empty `ι` also hold, because both sides are then trivial or zero.

### [`WeierstrassCurve.preΨ_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean#L314-L318) — `mathlib-0123`

Snippet: `samples/mathlib/mathlib-0123.lean`

- `[Nontrivial R]` (theorem): The hypothesis h : (n : R) ≠ 0 already implies Nontrivial R. In a trivial ring every element equals 0, so (n : R) = 0 and h would be false. Concretely, ⟨⟨(n : R), 0, h⟩⟩ : Nontrivial R. The statement therefore stays true after deleting the instance. The proof changes by first establishing `haveI : Nontrivial R := ⟨(n : R), 0, h⟩` and then running the same argument, so that the Nontrivial instance is available for `W.preΨ'_ne_zero` and for the inductive step. In the induction's neg case the instance is derived inside from the hypothesis for that case. I did not read the sources, so I did not check how `preΨ'_ne_zero` takes its Nontrivial assumption. I assumed it is an instance argument that the local `haveI` supplies.

### [`AdicCompletion.tensor_map_id_left_injective_of_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean#L367-L373) — `mathlib-0139`

Snippet: `samples/mathlib/mathlib-0139.lean`

- `[Module.Finite R M]` (variable): The statement does not need it to elaborate: it only mentions `AlgebraTensorModule.map LinearMap.id f`. It is true without it, because `AdicCompletion I R` is flat over a Noetherian ring `R`. Mathlib already derives this as `flat_of_isNoetherian`, using `Module.Flat.iff_lTensor_injective'` with ideals `J`, which are finite modules. The general statement then follows from `Module.Flat.lTensor_preserves_injective_linearMap`, which needs no finiteness. Its conclusion is injectivity of `f.lTensor (AdicCompletion I R)`, which is the same function as `AlgebraTensorModule.map LinearMap.id f` (the coercion differs by `rfl` or a simp lemma). The proof changes: keep the current argument as a private finite-case lemma used only for ideal inclusions, prove flatness from it, and derive this lemma from flatness. The `[Module.Finite R M]` argument can be dropped by `omit ... in`. Since `M`, `N` live in `Type u`, the universe constraints of the flatness lemma are no obstacle. Deleting `[Module.Finite R N]` is equally possible via the same flatness route, and each can be removed on its own or both together.
- `[Module.Finite R N]` (variable): The statement mentions neither finiteness of `N` nor anything that needs it. The result holds for arbitrary `R`-modules `M`, `N` once `R` is Noetherian, because `AdicCompletion I R` is flat over `R`. The proof goes through `Module.Flat.lTensor_preserves_injective_linearMap` applied to `f` with `Module.Flat R (AdicCompletion I R)`. To avoid circularity with `flat_of_isNoetherian`, which currently calls this lemma with `N = R` (finite because `R` is Noetherian), restructure the file: first a private finite-case lemma, then flatness, then this lemma. Deleting it is independent of deleting `[Module.Finite R M]`.

### [`continuous_parametric_integral_of_continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/Bochner/Set.lean#L1121-L1139) — `mathlib-0190`

Snippet: `samples/mathlib/mathlib-0190.lean`

- `[LocallyCompactSpace X]` (theorem): Local compactness is used only to get a compact neighbourhood U of x₀, so that ‖f‖ is bounded on U ×ˢ s. That bound holds without it. Since s is compact, {x₀} ×ˢ s is compact. ‖f.uncurry‖ is continuous, so it is bounded there by some M (e.g. via `IsCompact.bddAbove_image`). The set {p | ‖f.uncurry p‖ < M+1} is open and contains {x₀} ×ˢ s. `generalized_tube_lemma` (Mathlib/Topology/Compactness/Compact.lean) gives an open u ∋ x₀ and an open v ⊇ s with u ×ˢ v ⊆ that set. Take u in place of U. Then ‖f x y‖ ≤ M+1 for x ∈ u and y ∈ s, and u ∈ 𝓝 x₀. The rest of the proof is unchanged: `continuousAt_of_dominated` only needs [FirstCountableTopology X], and the constant bound is integrable on s because s is compact and μ is locally finite. The statement is therefore still true and provable with this one hypothesis deleted. Nothing else in the statement mentions LocallyCompactSpace X. The degenerate cases (X empty, s empty, E trivial) are all fine.

### [`DifferentiableOn.continuousMultilinear_apply_const`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean#L208-L211) — `mathlib-0251`

Snippet: `samples/mathlib/mathlib-0251.lean`

- `[Finite ι]` (variable): The statement elaborates and is true without `[Finite ι]`. `DifferentiableOn 𝕜 c s` is defined in the TVS section of `FDeriv/Defs.lean`, which needs only AddCommGroup, Module and TopologicalSpace on the codomain. The topology on `ContinuousMultilinearMap 𝕜 M H` (`ContinuousMultilinearMap.instTopologicalSpace`, in `Topology/Algebra/Module/Multilinear/Topology.lean`) needs no finiteness of `ι`. The `NormedAddCommGroup` instance needs `Fintype ι`, which `[Finite ι]` does not provide, so the statement already uses the general topological instance. The map `ContinuousMultilinearMap.apply 𝕜 M H u` is a continuous linear map for any `ι`. Proof without the hypothesis: for `x ∈ s`, take `c'` with `HasFDerivWithinAt c c' s x`, and let `g := ContinuousMultilinearMap.apply 𝕜 M H u`. Then `(c y) u - (c x) u - (g ∘L c') (y - x) = g (c y - c x - c' (y - x))`. By `ContinuousLinearMap.isBigOTVS_comp` (the same step used in `HasFDerivAtFilter.comp`) this is `=O` of `c y - c x - c' (y - x)`, which is `=o` of `y - x` by `hasFDerivWithinAt_iff_isLittleOTVS`. So `g ∘L c'` is the derivative of `fun y ↦ (c y) u` within `s` at `x`. The existing proof goes through `HasFDerivWithinAt.continuousMultilinear_apply_const`, which takes `[Fintype ι]`, and through `HasFDerivWithinAt.comp`, which takes a normed middle space, so the proof would have to redo the `isLittleOTVS` argument by hand. No degenerate case (empty `ι`, empty `s`) breaks it. I could not run Lean, so I did not check that the hand-written proof compiles.


## Tau Ceti (12 flagged)

### [`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/Basic.lean#L952-L963) — `tauceti-0001`

Snippet: `samples/tauceti/tauceti-0001.lean`

- `(hN : N ≠ 0)` (theorem): The statement also holds for N = 0, so the hypothesis can be dropped. For N = 0 we have primeFactors 0 = ∅, so both products are 1. The claim becomes (Gamma0 0).index = 0, because the right side is 0 * 1 = 0. Gamma0 0 is the subgroup of matrices in SL₂(ℤ) with lower-left entry c ≡ 0 mod 0, that is c = 0. It has infinite index. The matrices gₙ = [[1,0],[n,1]] have first columns (1,n). Left cosets g·Γ₀(0) are determined by the first column of g up to sign, because g·Γ₀(0) = g'·Γ₀(0) iff g⁻¹g' has c = 0 iff g'e₁ = ±g e₁. The first columns (1,n) are pairwise distinct up to sign, so the gₙ lie in infinitely many distinct cosets. Mathlib's `Subgroup.index` is 0 for infinite index, so the claim holds. For the proof, split on N = 0. When N ≠ 0, use the existing proof. When N = 0, simp reduces the goal to `(Gamma0 0).index = 0`, which follows from the infinite-index argument above, for example via `Subgroup.index_eq_zero_iff_infinite` or `Subgroup.finiteIndex_iff` plus an injection ℕ → SL₂(ℤ)/Γ₀(0). I did not run Lean to check this.

### [`HeckeRing.GLn.posDetInt_le_commensurator`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/HeckeRing/GLn/Basic.lean#L712-L717) — `tauceti-0020`

Snippet: `samples/tauceti/tauceti-0020.lean`

- `[NeZero n]` (variable): The statement `posDetInt n ≤ (commensurator (SLnZ n)).toSubmonoid` elaborates without `NeZero n`. `SLnZ` (line 74) and `posDetInt` (line 257) are defined before the first `variable [NeZero n]` at line 460, and they only need `Fin n`. The statement is also true for `n = 0`. `GL (Fin 0) ℚ` is the unit group of `Matrix (Fin 0) (Fin 0) ℚ`, which has one element, so it is a subsingleton group. Every element is `1`, and `1` lies in the commensurator (`one_mem`). Hence the inequality holds trivially for `n = 0`. For `n ≠ 0`, the current proof still works. Use `omit [NeZero n] in`, split on `n = 0` versus `n ≠ 0`, and in the second case supply `haveI : NeZero n := ⟨hn⟩` before applying `mem_commensurator_of_hasIntEntries n hg.1`. The only place `NeZero n` is really used is `conj_mat_det_one`, for `n - 1 + 1 = n` in the determinant computation. That lemma is itself only needed for `n ≠ 0`.

### [`TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Data/Nat/Factorization/GcdSplit.lean#L56-L71) — `tauceti-0078`

Snippet: `samples/tauceti/tauceti-0078.lean`

- `(hp : p.Prime)` (theorem): hp can be deleted. If p is not prime, then `Nat.factorization m p = 0` and `Nat.factorization n p = 0`, because the factorization is supported on primes (`Nat.factorization_eq_zero_of_not_prime`). That covers p = 0 and p = 1 as well. Then `ordCompl[p] m = m / p^0 = m` and `ordCompl[p] n = n`. The right side becomes `gcd m n * p ^ min 0 0 = gcd m n * 1 = gcd m n`, so the statement holds trivially. The proof splits with `by_cases hp : p.Prime`. The prime case is the existing proof. The non-prime case is `simp [Nat.factorization_eq_zero_of_not_prime _ hp]`. The hypotheses hm and hn must stay. For m = 0 and p ∣ n with p prime, the left side is n, while the right side is `n / p^v * 1`, which differs when v > 0. Symmetrically, hn must stay.

### [`LipschitzWith.ae_finite_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Function/AreaFormula/Real.lean#L119-L126) — `tauceti-0115`

Snippet: `samples/tauceti/tauceti-0115.lean`

- `(hs : NullMeasurableSet s volume)` (theorem): The hypothesis can be dropped. Let t := toMeasurable volume s. Then t is measurable (`measurableSet_toMeasurable`) and s ⊆ t (`subset_toMeasurable`). The volume on the finite-dimensional inner product space U is σ-finite, hence s-finite. So `Measure.restrict_toMeasurable_of_sfinite` gives volume.restrict t = volume.restrict s, with no measurability assumption on s. `IntegrableOn g s` is by definition `Integrable g (volume.restrict s)`. So the hypothesis `hint` for s gives `IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet) t`. The existing proof (via `ae_summable_fiber` with `hs := (measurableSet_toMeasurable ..).nullMeasurableSet`) applies to t, so almost every fiber `t ∩ f ⁻¹' {y}` is finite. Since s ∩ f ⁻¹' {y} ⊆ t ∩ f ⁻¹' {y}, the s-fibers are also finite for the same y (`Set.Finite.subset`). The statement is therefore true and provable without `hs`. The conclusion does not mention `hs`, and the other arguments do not depend on it.

### [`TauCeti.exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Cohomology.lean#L195-L206) — `tauceti-0118`

Snippet: `samples/tauceti/tauceti-0118.lean`

- `[CharZero K]` (variable): The statement does not need `CharZero K`. It only mentions `Rep.res`, `groupCohomology`, `Nat.card`, `padicValNat` and `padicCompletionUnitsRepresentation p L K`. The representation is defined in `MultiplicativeCompletion/Basic.lean` under `CommSemiring`/`Algebra` assumptions only, with no `CharZero`. The proof uses the hypothesis only through the private lemma `groupCohomology_res_padicCompletionUnits`, and there only as an instance argument. That instance is implied by the other hypotheses, because `[Algebra K L]` and `[CharZero L]` are both in scope. The map `algebraMap K L` is a ring hom out of a field, so it is injective (`(algebraMap K L).injective`). Mathlib's `RingHom.charZero_iff (f) (H : Function.Injective f) : CharZero R ↔ CharZero A` then gives `CharZero K` from `CharZero L`. For example, the proof can start with `haveI : CharZero K := (RingHom.charZero_iff (algebraMap K L).injective).mpr inferInstance`, and the rest is unchanged. So with `omit [CharZero K] in` the theorem stays true and provable. This is a statement about `Prop`-valued data, so no instance diamond arises. The related `CharZero L` is not removable in the same way, because `CharZero K` does not give `CharZero L` here without further argument. I did not check whether it is needed.

### [`Matrix.ProjectiveSpecialLinearGroup.isParabolic_inv_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup/FinTwo.lean#L103-L117) — `tauceti-0134`

Snippet: `samples/tauceti/tauceti-0134.lean`

- `[NoZeroDivisors R]` (variable): The statement does not need it. `Matrix.ProjectiveSpecialLinearGroup.IsParabolic` is defined before the `variable [NoZeroDivisors R]` line. It says ∃ a : SL(2,R), (a : PSL) = g ∧ (a : GL (Fin 2) R).IsParabolic, and it needs only `CommRing R`. The instance is used in the proof only through `isParabolic_mk_iff`, which says every representative is parabolic. That lemma is not needed here, because the statement is an iff and one direction suffices. At matrix level, `a` is parabolic iff `a⁻¹` is, over any commutative ring. `Matrix.IsParabolic m` is `m ∉ range scalar ∧ m.discr = 0`. For `a : SL(2,R)`, `a⁻¹` is `adjugate a = [[d,-b],[-c,a]]`. This is scalar iff b = 0, c = 0, a = d, and the same holds for `a`. The trace is the same and det = 1, so the discriminant is the same. The existing `simp only [...]` block (the `hscalar` lemma, `discr_fin_two`, `adjugate_fin_two`, `trace_fin_two`, `det_fin_two`) already proves this and uses no `NoZeroDivisors`. Without the instance, one direction is direct: from `IsParabolic g` take `⟨a, rfl, ha⟩`. Then `(a⁻¹ : PSL) = g⁻¹` by `QuotientGroup.mk_inv`, and `a⁻¹` is parabolic by the matrix-level fact. So `IsParabolic g → IsParabolic g⁻¹` holds. The converse is the same implication applied to `g⁻¹`, rewritten with `inv_inv`. There are no degenerate cases to check, since `IsParabolic` does not depend on the instance. To remove the instance, use `omit [NoZeroDivisors R] in`, as the file already does for later lemmas.

### [`TauCeti.IsFiniteType.exists_chain_of_reachable`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/FiniteType/Diagram.lean#L154-L185) — `tauceti-0149`

Snippet: `samples/tauceti/tauceti-0149.lean`

- `(h : IsFiniteType A)` (theorem): The conclusion only talks about the entries A (w i) (w j), so it holds for every integer matrix A. Let D be the directed relation i → j iff A i j ≠ 0. By `diagramGraph_adj`, a graph edge gives A i j ≠ 0 and A j i ≠ 0, so the Reachable hypothesis gives a D-path from u to v. Take a shortest D-path w₀ = u, …, wₙ = v, with n = 0 if u = v. Injectivity on {i ≤ n} follows from minimality, since a repeated vertex could be cut out. Each step satisfies A (w i) (w (i+1)) ≠ 0. For i + 1 < j ≤ n, a nonzero A (w i) (w j) would give a strictly shorter D-path, so it is 0. The proof does not need acyclicity of the diagram. In the current proof, `h` is used only through `diagramGraph_adj_iff`, to drop one of the two nonzero conditions, and through `isAcyclic_diagramGraph`. Both can be replaced by this shortest-path argument. The type of `h` mentions only `A`, which stays in the statement through `diagramGraph A`, so deleting `h` does not break elaboration.

### [`MeasureTheory.Measure.rnDeriv_mul_measure_singleton`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Measure/Decomposition/Lebesgue.lean#L46-L58) — `tauceti-0170`

Snippet: `samples/tauceti/tauceti-0170.lean`

- `[MeasurableSingletonClass α]` (variable): The statement only uses `{x}` as a set, so it elaborates without the instance. It is also still true without it, where `μ {x}` and `ν {x}` are outer-measure values. The only place the proof uses the instance is `measurableSet_singleton x` (in `withDensity_apply` and `lintegral_singleton`). The `hsing` part does not use it, because `measure_mono_null` and `add_apply` hold for arbitrary sets.

Write f := μ.rnDeriv ν; it is measurable (`measurable_rnDeriv`). The decomposition gives μ = singularPart + ν.withDensity f. Then:

1. `singularPart {x} = 0`. Take a measurable null set N of the singular part with ν Nᶜ = 0. If x ∈ N then {x} ⊆ N; otherwise {x} ⊆ Nᶜ gives ν{x} = 0, contradicting hx. This is exactly the existing `hsing` argument.

2. `(ν.withDensity f){x} = f x * ν{x}`.
   - (≤) Take a measurable t ⊇ {x} with ν t = ν{x} (`toMeasurable`). Let B = t ∩ {f ≤ f x}. B is measurable, contains x, and ν B = ν{x}, since ν{x} ≤ ν B ≤ ν t. Then (withDensity f){x} ≤ withDensity f B = ∫⁻_B f ≤ f x * ν B = f x * ν{x}.
   - (≥) Take a measurable C ⊇ {x} with (withDensity f) C = (withDensity f){x}. Let C' = C ∩ {f ≥ f x}. Then (withDensity f){x} ≥ withDensity f C' = ∫⁻_{C'} f ≥ f x * ν C' ≥ f x * ν{x}.
   - The cases f x = 0 and f x = ∞ are covered because only monotonicity is used, with no cancellation.

So the identity holds without measurable singletons, and the proof only needs this replacement for step 2. The other two hypotheses are needed. Without hx, take ν = 0 and μ = dirac x: the left side is 0 and the right side is 1. Without the Lebesgue decomposition, rnDeriv is the junk value 0. Counting measure on ℝ against Lebesgue + dirac 0 has no decomposition, yet ν{0} = 1 ≠ 0 and μ{0} = 1.

### [`TauCeti.exists_coprimePart_indK0_of_trivial_eq_nsmul`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/GrothendieckGroup/GroupAlgebra/Permutation/PrimePower.lean#L131-L148) — `tauceti-0194`

Snippet: `samples/tauceti/tauceti-0194.lean`

- `[Fact p.Prime]` (variable): The statement only uses p as a natural number (p ∣ Nat.card D, p ^ (Nat.card C).factorization p) and never uses the Fact. The Fact is recoverable from [CharP k p] with [Field k]. Mathlib's `CharP.char_is_prime_or_zero` gives `Nat.Prime p ∨ p = 0`. If p is prime, the existing proof goes through after `haveI := Fact.mk hp`. If p = 0, take D = C. Then `D ≤ C` holds. `¬ 0 ∣ Nat.card C` holds because C is finite, so its cardinality is nonzero. `C.relIndex C = 1`, and `0 ^ ((Nat.card C).factorization 0) = 0 ^ 0 = 1`, since `Nat.factorization` at a non-prime is 0. The last equation becomes `indK0 … = 1 • indK0 …`, which is true. So the theorem stays true and provable with `Fact p.Prime` omitted. I did not check each lemma in the p = 0 case against Lean, so this is the one point I am less sure of. CharP k p is genuinely needed: in characteristic 0 the statement fails, for example G = C = Z/p over Q.

### [`TauCeti.cwEulerChar_preimage_of_card_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/Covering.lean#L75-L88) — `tauceti-0231`

Snippet: `samples/tauceti/tauceti-0231.lean`

- `(hfin : ∀ b, Finite ↥(p ⁻¹' {b}))` (variable): The statement only mentions `cwComplexPreimage C hp` (which takes only `hp`, `C`, `T2Space B`) and `cwEulerChar`. `hfin` is used only through `nat_card_cell_preimage_of_card_fiber`, via `Nat.card_sigma`, which needs each fibre to be finite. Given `hd` this is derivable or irrelevant. Let `n` be fixed, `cell C n` is finite (`FiniteType.finite_cell`), and `cellPreimageEquiv C hp n : cell (p⁻¹' C) n ≃ Σ i, p⁻¹' {map n i 0}`. Each centre `map n i 0` lies in `C`, so `hd` gives `Nat.card (fibre) = d`. If `d ≠ 0`, every such fibre is finite (`Nat.card ≠ 0` implies `Finite`), so `Nat.card_sigma` applies exactly as before and gives `d * Nat.card (cell C n)`. If `d = 0`, every fibre over a centre is empty or infinite. If all are empty, the sigma type is empty and has card 0. If one is infinite, the sigma type is infinite and `Nat.card` is 0. In both cases the card is 0 = `0 * Nat.card (cell C n)`. So the cellwise equation `Nat.card (cell (p⁻¹' C) n) = d * Nat.card (cell C n)` holds without `hfin`. The rest of the proof uses only `FiniteDimensional.eventually_isEmpty_cell` for `C`, `cellPreimageEquiv`, and `cwEulerChar_eq_sum_range`, none of which use `hfin`. Fibres outside `C` do not appear in the statement. So `hfin` can be omitted, with the case split above replacing the call to `nat_card_cell_preimage_of_card_fiber C hp hfin hd`.

### [`TauCeti.schwarzChristoffelEdgeAngle_comp_strictMono`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/GlobalTurning.lean#L114-L125) — `tauceti-0238`

Snippet: `samples/tauceti/tauceti-0238.lean`

- `[LocallyFiniteOrder ι]` (variable): The statement (StrictMono of i ↦ schwarzChristoffelEdgeAngle a e (a i)) only needs Fintype ι (for the sum in the definition `π * ∑ i, if c < a i then e i else 0`) and LinearOrder ι (for StrictMono); it never mentions LocallyFiniteOrder. The instance is only used in the proof, to write the index interval Finset.Ioc i j. Without it the theorem is still true and provable: in the proof, use `classical` and take the lemma `schwarzChristoffelEdgeAngle_sub a e (ha.monotone hij.le)` (in Edge.lean, which needs no LocallyFiniteOrder). It gives angle(a j) - angle(a i) = -π * ∑ k ∈ univ.filter (fun k => a k ∈ Ioc (a i) (a j)), e k. This sum is negative by Finset.sum_neg, since every e k < 0 and the filter contains j (a i < a j by ha, and a j ≤ a j). Then nlinarith with Real.pi_pos finishes. This avoids Finset.Ioc entirely.

### [`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isCompact`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/PDE/Regularity/HolderContinuity.lean#L238-L258) — `tauceti-0281`

Snippet: `samples/tauceti/tauceti-0281.lean`

- `[Nonempty ι]` (theorem): The statement never mentions Nonempty ι. It is only used to call the `_drift` lemma, which also assumes it. Without it the theorem is still true. Split with `isEmpty_or_nonempty ι`. If ι is nonempty, the existing proof works unchanged. If ι is empty, `EuclideanSpace ℝ ι` has at most one point, since it is a `PiLp` over an empty index type and any two elements are equal by `ext` on the empty index. Take α = 1, which satisfies 0 < 1 ≤ 1. Then take C = 0. For any K, `HolderOnWith 0 1 f K` holds: for x, y ∈ K we have x = y, so `edist (f x) (f y) = 0 ≤ 0 * edist x y`. The remaining hypotheses are not needed in this case, and nothing in the statement is degenerate or false there.


## Lean Pool (39 flagged)

### [`ViscositySolns.exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Aleksandrov/JetCalculus/Strictification/StrictifiedObjective.lean#L337-L370) — `lean-pool-0000`

Snippet: `samples/lean-pool/lean-pool-0000.lean`

- `(hr : 0 <= r)` (theorem): CoordinateSemiconvexOn lambda C f is defined as ∀ x ∈ C, ∀ y ∈ C, ... so it holds vacuously when C is empty. If r < 0 then Metric.closedBall (0 : Point n) r = ∅ (Metric.closedBall_eq_empty), so any lambda (e.g. 0) works. The theorem is therefore true without hr. Proof: by_cases h : 0 ≤ r; in the positive case use the existing proof unchanged; in the negative case take lambda = 0 and discharge the membership x ∈ closedBall 0 r by rewriting closedBall as ∅ (Metric.closedBall_eq_empty.mpr (not_le.mp h)). The hypothesis hconv is still needed, so only hr is unnecessary.

### [`IsoGraph.Canon.splitCell_tr_general`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Equivariance.lean#L3331-L3342) — `lean-pool-0028`

Snippet: `samples/lean-pool/lean-pool-0028.lean`

- `(hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))` (theorem): The conclusion `(splitCell cnt c st).tr = tr` only involves `tr`, which hbd ties to `boundsFrom (sortNats ks0) sizes … st.cst st.cen #[] c (mixN st.tr c)`. In `splitCell` (Algorithm.lean:376) that call depends only on `ks0` (from hb) and `sizes` (from ho). It does not depend on the scatter or write results (`block`, `bc2`, `lab`, `pos`). `scatterFrom` is a total function, so its output pair exists. A proof can start with `obtain ⟨block', bc2', hsc'⟩ : ∃ b c', scatterFrom … = (b, c') := ⟨_, _, rfl⟩`, and the same pattern gives a `writeFrom` result. It then applies `splitCell_eq_general` with these actual values and reads off `tr` from the resulting record. This is the same pattern `splitCell_bc` uses for `hb`. The theorem stays true without hsc. Without it, `block` and `bc2` are not constrained, but hw would then ignore the real scatter output. The same pattern removes hw instead, so hsc and hw are each deletable alone.
- `(hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))` (theorem): `tr` in the conclusion and in hbd does not depend on `lab` or `pos`. The `boundsFrom` call uses only `ks0`, `sizes`, `st.cst`, `st.cen`, `st.tr` and `c`. `writeFrom` is total, so a proof can obtain an actual `(lab, pos)` by `⟨_, _, rfl⟩`, with `block` from the actual `scatterFrom` result. It then rewrites with `splitCell_eq_general hb h1 h2 ho hsc hw' hbd`, and `.tr` of the resulting record is `tr`. The theorem therefore stays true and provable without hw. Deleting hw leaves the statement well-formed, because `lab` and `pos` appear nowhere else in the statement.

### [`ESS.buCut_gradient_absorption`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUShortGradient.lean#L28-L102) — `lean-pool-0033`

Snippet: `samples/lean-pool/lean-pool-0033.lean`

- `(hM : 0 ≤ M)` (theorem): It follows from hderiv. Fin 3 is nonempty, so `(abs_nonneg _).trans (hderiv 0) : 0 ≤ M`. The proof can start with `have hM : 0 ≤ M := (abs_nonneg _).trans (hderiv 0)`, and the rest is unchanged.
- `(hκ : 0 ≤ buCutScalar κ z)` (theorem): The statement is still true without it. Write ξ = buCutScalar κ z. The right side 3*(sqrt(..) + M*‖v z‖) is nonnegative, because M ≥ 0 (from hderiv) and the norm and sqrt are nonnegative. If ξ < 0, the left side ξ*sqrt(..) is ≤ 0, so it is ≤ the right side. If ξ ≥ 0, the existing proof applies. The proof only used hκ in `hroot`, to rewrite |ξ| as ξ. The case split `by_cases ξ ≥ 0` replaces it: the negative case is closed by `mul_nonpos_of_nonpos_of_nonneg` together with `hU`. This deletion is independent of hM, because hM is derivable from hderiv.

### [`IsoGraph.Canon.individualize_refines`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Progress.lean#L192-L202) — `lean-pool-0038`

Snippet: `samples/lean-pool/lean-pool-0038.lean`

- `(hv : v < n)` (theorem): The statement stays true without `hv`. `individualize_cst_eq` (rfl) shows the new `cst` differs from `p.cst` only on `[c+1, ec)`, where `i = p.pos[v]!`, `c = p.cst[i]!` and `ec = p.cen[i]!`. If `v ≥ n`, then `hp.posSize` gives `p.pos.size = n`, so `p.pos[v]! = 0`. If `n = 0` the goal is vacuous (no `i < n`). If `n > 0`, then `i = 0 < n`. `cstLe` gives `c = 0`, and `ltCen`/`cenLe` give `0 < ec ≤ n`. For `1 ≤ k < ec`, `cellCst` at index 0 gives `p.cst[k]! = p.cst[0]! = 0 ≠ k`, so no start `k` with `p.cst[k]! = k` is overwritten. Hence `Refines` holds. The proof splits on `v < n`: the `v < n` case uses the existing proof. In the other case, rewrite `p.pos[v]! = 0` and use `individualize_cst_eq` with `setCstFrom_getElemD` (side condition `ec ≤ p.cst.size` from `hp.cenLe 0` and `hp.cstSize`), then the `cellCst` argument. `IndivData` itself needs `v < n`, so this case bypasses it. `hp` is still needed.

### [`TauCeti.DavisKahanExt.le_riccati_small_root_of_quadratic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Riccati/BoundedSharpEstimates.lean#L41-L89) — `lean-pool-0045`

Snippet: `samples/lean-pool/lean-pool-0045.lean`

- `(hd : 0 < d)` (theorem): hd is implied by hb : 0 ≤ b and hsmall : 2 * b < d, since d > 2b ≥ 0. Deleting it leaves the statement unchanged and true. In the proof, hsumpos : 0 < d + 2*b (currently by nlinarith) follows by linarith from hb and hsmall. Everything after that (hdiscpos, hden, etc.) uses only hsumpos, hsmall, hb, and the derived facts, so the proof goes through with `have hd : 0 < d := by linarith` added at the start.

### [`NavierStokes.HeatedOutgoing.E_times_U`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/HeatedOutgoing.lean#L1197-L1206) — `lean-pool-0047`

Snippet: `samples/lean-pool/lean-pool-0047.lean`

- `(hX : 0 < X)` (theorem): The statement stays true for every real X, so `hX` can be dropped. The proof has to change, because the current one passes through `heatE_times_U` and `heatE_before`, which both need `0 < X`.

Definitions. `U F XR (X,eta) = F.U (X/XR, eta) = F.logU (Real.log (X/XR), eta)`. `heatE = OutgoingDilation.E * HeatTailEdit.multiplier ... (switchRadius F XR) X`. The multiplier is `1 + switch K X * (...)`, and `switch K X = sigma (Real.log (X/K) / (3/10))`. Mathlib's `Real.log` satisfies `log x = log |x|`, so both `U` and `switch` depend on X only through |X|.

Proof without `hX`. Let K = switchRadius F XR; `OutgoingDilation.switchRadius_pos` gives K > 0 from `hXR`.
- Case |X| ≤ K. Then `Real.log (X/K) = Real.log (|X|/K) ≤ 0`; for X = 0 the log is 0. So `OutgoingSchedule.sigma_zero` gives `switch K X = 0` and the multiplier is 1. Hence `heatE F XR (X,eta) = OutgoingDilation.E F XR (X,eta)`, and the heat part of the identity is immediate. This is `HeatTailEdit.edit_before` with the positivity of X replaced by this log argument.
- Case K < |X|. Then `U F XR (X,eta) = U F XR (|X|,eta)`, by `Real.log_abs` and `abs_div` with XR > 0. `OutgoingDilation.after_pulse` at |X| > 0 needs `pulseEndRadius ≤ |X|`, and `pulseEnd_le_switch` gives that. So `U F XR (X,eta) = 0` and both sides are 0. `U_after_switch` is the same fact stated for positive X.
- The patch part does not use `hX`. `OutgoingDilation.correction_times_U_zero F XR eta X hXR` has only the hypothesis `0 < XR`, so `patchIncrement * U = 0` holds for all X.

The rest of the proof (`E`, `add_mul`, `hp`, `add_zero`) is unchanged. `hXR` is still used.

### [`RS.tensorPow_id_ne_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/SuperEmbed/Standard.lean#L336-L359) — `lean-pool-0048`

Snippet: `samples/lean-pool/lean-pool-0048.lean`

- `[MonoidalPreadditive A]` (theorem): The statement doesn't need this instance to elaborate. `tensorPow` needs only `Category` and `MonoidalCategory`, and the `0` morphism needs only `Preadditive`. The proof uses it in one place, `MonoidalPreadditive.zero_whiskerRight`, to turn `𝟙 (T_k ⊗ U ...) = 𝟙 T_{k+1} ▷ U` with `𝟙 T_{k+1} = 0` into `0`. That step can be done without the instance.

In a preadditive category, `𝟙 X = 0` holds exactly when `X` is a zero object (`Limits.IsZero.iff_id_eq_zero`, which the proof already uses). So the successor step reduces to showing that `X ⊗ U` is a zero object when `X` is.

This follows because `G = (- ⊗ U)` is fully faithful when `U ⊗ U ≅ 𝟙_ A`. Since `(X ⊗ U) ⊗ U ≅ X ⊗ (U ⊗ U) ≅ X ⊗ 𝟙_ A ≅ X` naturally, `G ∘ G ≅ 𝟙`, so `G` is an equivalence. If `X` is a zero object, then `End(X)` is a singleton. Hence `End(X ⊗ U)` is a singleton, so `𝟙 (X ⊗ U) = 0`.

The rest of the proof is unchanged: transfer along the isomorphism `T_{k+1} ⊗ U ≅ T_k` via `id_zero_transfer`, which needs only `Preadditive`, then apply the induction hypothesis. The base case, `hone`, and `hUU` don't use the instance. So the theorem stays true and provable after removing `[MonoidalPreadditive A]`.

### [`EulerOrdinarySobolev.Evolution.gradient_logarithmic_envelope`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/OrdinaryEulerBKM.lean#L109-L141) — `lean-pool-0078`

Snippet: `samples/lean-pool/lean-pool-0078.lean`

- `(hC : 0 ≤ C)` (variable): hC is only used in the proof, at mul_le_mul_of_nonneg_left (… ) hC. It is not mentioned in the statement or in any other binder (hW and hlog only mention C as a term). It follows from hlog and hW. Take t = ⟨0, le_rfl, hT⟩, which exists since Icc 0 T is nonempty. Then 0 ≤ U.gradientNormPath t (by gradientNormPath_nonneg), and hlog t gives U.gradientNormPath t ≤ C * B, where B = 1 + ‖(U.velocity t).toLp‖ + W t * log (exp 1 + tensorNorm 3 (U.velocity t)). B ≥ 1 > 0: the norm is ≥ 0, W t ≥ 0 by hW, tensorNorm_nonneg gives exp 1 + tensorNorm ≥ exp 1, so log(…) ≥ log(exp 1) = 1 ≥ 0. So 0 ≤ C * B with B > 0, hence 0 ≤ C. The proof can start with `have hC : 0 ≤ C := nonneg_of_mul_nonneg_left …` using this argument (or equivalent), and the rest is unchanged. The theorem is therefore true and provable after deleting hC with `omit hC in`.

### [`RS.kernelSubobject_tensorHom_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/KernelPow.lean#L729-L761) — `lean-pool-0091`

Snippet: `samples/lean-pool/lean-pool-0091.lean`

- `[Epi p₁]` (theorem): The statement elaborates without it, and it appears to be true in general; I did not prove the general case in Lean. The only place the proof uses it is `epi_whiskerRight_of_epi p₁` for the covering hypothesis `hv`. Without it, factor p₁ = e ≫ m with e epi and m mono (image factorisation in the abelian category). In a rigid category `m ▷ W₂` is mono, since tensoring is exact, i.e. `tensorRight` preserves limits. Since p₁ ⊗ₘ p₂ = (e ▷ Z₂) ≫ (I ◁ p₂) ≫ (m ▷ W₂), the kernel of p₁ ⊗ₘ p₂ equals the kernel of (e ▷ Z₂) ≫ (I ◁ p₂). The existing argument applied to the epi e (with I in place of W₁) bounds this by ker(e ▷ Z₂) ⊔ im(Z₁ ◁ ker ι p₂), and `kernelSubobject_whiskerRight_le` bounds ker(e ▷ Z₂) by im(kernel.ι e ▷ Z₂). Since m is mono, kernel.ι e and kernel.ι p₁ differ by an isomorphism, so the images of their whiskerings agree. Degenerate check: if p₁ = 0 then kernel.ι p₁ is an isomorphism, so the right side is ⊤ and the claim holds.

### [`Egrs75.ClearingP3.lowDigits_half_pred_pow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Egrs75/SubtractBranch.lean#L172-L181) — `lean-pool-0093`

Snippet: `samples/lean-pool/lean-pool-0093.lean`

- `(hp : 3 ≤ p)` (theorem): `Odd p` already gives p ≥ 1 and p ≠ 0, 2, so the only value `3 ≤ p` excludes is p = 1. For p = 1 the claim still holds: (1^m - 1)/2 = 0, and `LowDigits 1 0` is `∀ d ∈ Nat.digits 1 0, d ≤ 0`. This is true because `Nat.digits 1 0 = []`. A proof can case on p = 1. In that case, subst, simp [one_pow] and use `RoundUp.lowDigits_zero`. Otherwise, derive `3 ≤ p` from `hodd` (obtain ⟨k, hk⟩ := hodd; omega, using p ≠ 1) and run the existing induction. The existing induction only uses hp to get 2 ≤ p, which follows from that derived bound.

### [`NFChoice.Compiler.NFCompactLeafFinalGate.axSiCompact`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NFWeakPartition/NFCompactLeafFinalGate.lean#L209-L255) — `lean-pool-0096`

Snippet: `samples/lean-pool/lean-pool-0096.lean`

- `(hzw : z ≠ w)` (theorem): The proof uses hzw only to show v' z = Z (update at w does not clobber z). If z = w, the inner quantifier `.all w` shadows `.all z`, so the statement reduces to ∃ y ∀ W, (⟨{W},{W}⟩ ∈ y ↔ ⟨W,W⟩ ∈ x). This is still true: it is the Z = W instance of the axiom instance hY, which the proof already obtains as `hY Z W` for all Z W. Proof without hzw: do `by_cases hzw : z = w`. In the case z = w, subst it, use `hY W W` with v' z = W = lookup xs 1 (xs built from W, W), and the rest is unchanged. Otherwise the existing proof runs. The other disequalities are not removable. If x = y, x = z or x = w, then x in the body is captured by a binder and the statement becomes false. If y = z or y = w, the statement is also false in general.

### [`NavierStokes.TerminalCompensation.physicalProfile_family_contDiffOn`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalCompensation.lean#L1082-L1099) — `lean-pool-0105`

Snippet: `samples/lean-pool/lean-pool-0105.lean`

- `(hR : 0 < R)` (theorem): The statement is true for every real R. `physicalProfile P lam R a c X = a * (baseProfile lam (X/R) + correction P c (X/R))`, and `baseProfile lam x = x ^ slope lam` is a real power. The proof only uses `hR` in `hb`, to show `z.2 / R ≠ 0`. The hypothesis is not needed.

- **R ≠ 0:** on `U ×ˢ Ioi 0` we have `z.2 ≠ 0`, so `z.2 / R ≠ 0`. `Real.contDiffAt_rpow_const_of_ne` only assumes `x ≠ 0` (it is stated for any real x), so it covers R < 0 too. Replace `(div_pos hz.2 hR).ne'` with `div_ne_zero hz.2.ne' hR.ne`.
- **R = 0:** `z.2 / 0 = 0`. The function `z ↦ baseProfile lam (z.2/R)` is then the constant `baseProfile lam 0`, so it is smooth by `contDiffOn_const`. The `hr` step never uses `R > 0`: it composes `correction_family_contDiffOn` with `(z.1, z.2/R)`, which is smooth for any R. The final `ha'.mul (hb.add hr)` is unchanged.

So a case split on `R = 0` gives the theorem without `hR`.

### [`NavierStokes.PolarCharts.chart_finiteJets_uniform`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalGraphBounds.lean#L336-L354) — `lean-pool-0108`

Snippet: `samples/lean-pool/lean-pool-0108.lean`

- `(ha : 0 < a)` (theorem): The proof uses `ha` only to get `chart_contDiff ha j : ContDiff ℝ ∞ (chart a j)`. The rest is a compactness argument. `chart a j` is smooth for every real `a`, so the statement holds without `ha`. `chart a j p = ((extendedBase a (rotate j p)).1, (extendedBase a (rotate j p)).2 + offset j)`, with `extendedBase a p = (√(positiveRadius (a^2/32) (p.1^2+p.2^2)), arctan (p.2 / positiveRadius (a/8) p.1))`, and `positiveRadius ℓ x = ℓ + (x-ℓ) * smoothTransition ((x-ℓ)/ℓ)`. `positiveRadius_contDiff` holds for every `ℓ`. The only place positivity matters is that the two denominators and the sqrt argument must be nonvanishing, or the function must be constant. Case a = 0: `positiveRadius 0 x = 0 + x * smoothTransition (x/0) = x * smoothTransition 0 = 0`. So the sqrt argument is the constant 0, and the arctan argument is `p.2/0 = 0`. Both coordinates are constant, hence smooth. Case a < 0: `a^2/32 > 0`, so the sqrt part is handled by `positiveRadius_pos` as before. For `ℓ = a/8 < 0`, `positiveRadius ℓ x < 0` for all `x`. If `x ≥ ℓ` then `(x-ℓ)/ℓ ≤ 0`, so the transition is 0 and the value is `ℓ < 0`. If `x < ℓ` then `x-ℓ < 0` and `smoothTransition ∈ [0,1]`, so the value is `ℓ + (negative) ≤ ℓ < 0`. So the denominator never vanishes and `ContDiff.div` applies. Hence `chart_contDiff` holds for all `a`, via a case split on the sign of `a`. The rest of the proof (`continuous_iteratedFDeriv`, `exists_bound_of_continuousOn` on the compact closed ball, the finite sum over `Index × Fin (m+1)`) never mentions `a` or `ha`. So the theorem is true and provable without `ha`; the proof only needs a smoothness lemma for `chart a j` valid for all `a`.

### [`NavierStokes.SlowStressSupport.axial_stress_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SlowStressSupport.lean#L2093-L2133) — `lean-pool-0111`

Snippet: `samples/lean-pool/lean-pool-0111.lean`

- `(hn : 0 < n)` (theorem): The proof uses hn only in `hprev_le : n - 1 ≤ n := (Nat.sub_lt hn (by decide : 0 < 1)).le`. That fact holds for every n, since truncated subtraction gives n - 1 ≤ n, including n = 0. It can be proved by `Nat.sub_le n 1` (the proof already uses `Nat.sub_le _ _` in other places). hn is not passed to any other lemma: `smooth_axialDensity`, `axial_integral_zero`, `exterior_axialDensity`, `stress_smooth` and the rest all take other arguments. n appears in the statement independently of hn, so deleting hn leaves the statement unchanged and the proof goes through with that one replacement.

### [`CKN.Leray.mildShiftedStokesIntegral_continuous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierMildIntegral.lean#L216-L225) — `lean-pool-0117`

Snippet: `samples/lean-pool/lean-pool-0117.lean`

- `(hC : 0 ≤ C)` (theorem): hFC says ∀ t, ‖F t‖ ≤ C. Taking t = 0 gives 0 ≤ ‖F 0‖ ≤ C, so 0 ≤ C follows from hFC, i.e. `(norm_nonneg _).trans (hFC 0)`. The theorem is stated for `F : ℝ → RealTensorL2`, whose domain ℝ is nonempty. So the proof can start with `have hC := (norm_nonneg _).trans (hFC 0)` and then call mildShiftedStokesIntegral_continuousAt as before. The statement is unchanged.
- `(hT : 0 ≤ T)` (theorem): The integrand mildShiftedStokesIntegrand F t τ is defined as 0 unless 0 < τ ∧ τ < t. If T < 0, the integral ∫ τ in 0..T is over Ioc T 0, where τ ≤ 0. The integrand is therefore identically 0 there, so the integral is 0 for every t and the function is constant, hence continuous. If 0 ≤ T, the existing proof applies. So the proof is a case split on T: the case T < 0 shows the function is constantly 0, and the case 0 ≤ T uses mildShiftedStokesIntegral_continuousAt. This hypothesis can be removed on its own. It can also be removed together with hC, because hC is derivable from hFC.

### [`ESS.buGaussian_shifted_trace_strip_tendsto`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUGaussianAverageTools.lean#L334-L436) — `lean-pool-0118`

Snippet: `samples/lean-pool/lean-pool-0118.lean`

- `(hB : MeasurableSet B)` (theorem): hB is used only to supply `hB.prod measurableSet_Ioc` to the two `setIntegral_congr_ae` calls (hleft and hright). In both calls the integrands agree at every point, not just on the set. In hleft, after `rw [hτsymm, parabolicHomeomorph_symm_apply]` the goal is closed by `buGaussian_timeShift_point_symm_apply σ q`, which is stated for every point and takes no membership hypothesis. The hypothesis `hqmem` is never used. In hright, `simp [F]` closes the goal pointwise. So both calls can be replaced by the non-set version `integral_congr_ae` with `Filter.Eventually.of_forall`, or by rewriting with `funext`, and no measurability is needed. The other steps do not need it either. `MeasurePreserving.setIntegral_image_emb` takes a measurable embedding and no measurability of the set. `setIntegral_parabolic_to_product` has no hypotheses. `himage` is purely set-theoretic. The theorem is therefore provable, and so true, without hB.

### [`NavierStokes.PressureStream.reconstructed_divergence_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PressureStream.lean#L773-L791) — `lean-pool-0120`

Snippet: `samples/lean-pool/lean-pool-0120.lean`

- `(hab : a < b)` (theorem): The statement is still true without `hab`, and `hab` appears nowhere else in the statement. Split on whether `a < b` holds. If it does, run the existing proof unchanged. If `b ≤ a`, then `Icc a b ⊆ {a}`. The hypothesis `hs` says `support γd ⊆ Prod.fst ⁻¹' Icc a b`. Since `γd` is continuous (from `hγ`), its support is open. The first projection `ℝ × E → ℝ` is an open map, so the image of the support is an open subset of `{a}` and is therefore empty. Hence `γd = 0`. Then `weightedSource γd = fun p => p.1 * 0 = 0`, `normalizeSource d a 0 = sourceMultiplier • 0 = 0`, and `pastIntegral` and `totalIntegral` of the zero function are integrals of 0, hence 0. So `compactIntegral` is `0 - χ • 0 = 0`, `pullback` of 0 is 0, and `divideRadius 0 = 0`. This gives `streamPotential d a b M v γd = 0`. Next, `streamBeta w 0 = -graphDz w 0 = 0` and `streamGamma k v 0 = graphDr k v 0 + 0 = 0`, because `fderiv ℝ 0 p = 0`. Finally `graphDivergence … = 0 + 0/p.1 + 0 = 0`. The other hypotheses (`ha`, `hd`, `hγ`, `hs`) are all still available for this case. `hab` is used only to feed `streamPotential_supported` and `reconstructed_divergence_zero_of_ne`, which the `a < b` branch can still call.

### [`PDL.localInterpolantStep_oneSidedR`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/Local.lean#L307-L366) — `lean-pool-0128`

Snippet: `samples/lean-pool/lean-pool-0128.lean`

- `(def_rule : rule = LocalRule.oneSidedR orule YS_def)` (theorem): def_rule is mentioned nowhere in the statement. It is used only once in the proof, in `have c_in' : ((L', R', o') : Sequent) ∈ C := hC ▸ def_rule ▸ c_in`. `applyLocalRule` (Local/Rules.lean:326) matches its rule argument with `_`, so its value does not depend on the rule. `applyLocalRule rule (L,R,o)` is therefore definitionally equal to `applyLocalRule (LocalRule.oneSidedR orule YS_def) (L,R,o)`, because both rules have the same type `LocalRule (∅, Rcond, none) ress_1`. The proof already relies on this earlier. In `same_L` and the first bullet it writes `hC ▸ c_in` for `oneSidedR_preserves_left`, which expects membership in `applyLocalRule (LocalRule.oneSidedR orule YS_def) _`. Nothing there uses def_rule. In the third bullet, `c_in : (L',R',o') ∈ applyLocalRule (LocalRule.oneSidedR orule YS_def) ⟨L,R,o⟩` comes from `oneSidedR_sat_down`. So `c_in'` can be proved as `by rw [hC]; exact c_in`, or `hC ▸ c_in`, with no def_rule. The theorem is still true without def_rule and the proof barely changes. The `rule` binder itself must stay, because hC mentions it.

### [`GerverSofa.PartC.Stage2.rhoC_nonneg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MovingSofa/GerverSofa/KernelOnly/Core/Bundle006.lean#L896-L906) — `lean-pool-0129`

Snippet: `samples/lean-pool/lean-pool-0129.lean`

- `(ht : t ∈ Set.Icc (0 : ℝ) T)` (theorem): The hypothesis is only used for `ht.1 : 0 ≤ t`, in the phase-2 and phase-3 branches. In `rhoC`, the first branch (`t ≤ params.phi`) gives the constant 1/2. Every later branch is reached only when `¬ t ≤ params.phi`, so `params.phi < t`. The lemma `phi_nonneg : 0 ≤ params.phi` (line 662, no arguments) then gives `0 ≤ t`. In the proof, `hφ : ¬ t ≤ params.phi` is in context after `split_ifs`. So `have ht0 : 0 ≤ t := le_trans phi_nonneg (le_of_lt (lt_of_not_ge hφ))` replaces `ht.1` in the phase-2 and phase-3 calls to `rhoC_phase2_nonneg` and `rhoC_phase3_nonneg`. The phase-4 branch already derives `0 ≤ t` from `eta ≤ t` (it never uses `ht`). The last branch is 0. The upper bound `t ≤ T` is never used. So the statement `∀ t, 0 ≤ rhoC t` holds without the hypothesis. `T` is still needed by `rhoC` through `tau` and `eta`, so deleting the binder does not break elaboration.

### [`AVenhance.Infra.Section5.Contracts.sds_gradMatrix_entry_periodic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/Contracts/TermCenteredAnalyticSmooth.lean#L49-L57) — `lean-pool-0130`

Snippet: `samples/lean-pool/lean-pool-0130.lean`

- `(hF : Differentiable ℝ F)` (theorem): Differentiability is not needed. Fix i j and k, and let g y := F y j. Applying `he` at coordinate j gives g (y + latticeShift k) = g y + (k j : ℝ) for all y. The goal unfolds to fderiv ℝ g (x + latticeShift k) (basisVec i) = fderiv ℝ g x (basisVec i); `gradMatrix` and `spaceGrad` are defined with `fderiv`, which is 0 at non-differentiable points. It suffices to show fderiv ℝ g (x + latticeShift k) = fderiv ℝ g x. Mathlib's `fderiv_comp_add_right` (no differentiability hypothesis) gives fderiv ℝ g (x + a) = fderiv ℝ (fun y => g (y + a)) x. Rewriting with the identity above turns the right side into fderiv ℝ (fun y => g y + c) x, and `fderiv_add_const` (also with no differentiability hypothesis) turns that into fderiv ℝ g x. The case where g is not differentiable at x is covered, because then g is not differentiable at x + k either and both sides are 0. The remaining hypothesis `he` is still needed. The current proof uses `hF` only for `amnr_fderiv_periodic_of_equivariant` and `fderiv_apply`; the argument above replaces both.

### [`polytopeRoundedSupportCurve_regular`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OperatorTheory/Operator/Crouzeix/SmoothSupportCurve.lean#L231-L242) — `lean-pool-0133`

Snippet: `samples/lean-pool/lean-pool-0133.lean`

- `(hu : u.Nonempty)` (theorem): The statement is still true for u = ∅. Then polytopeSoftPartition ∅ delta theta is an empty sum, so it is 0. Hence polytopeSoftSupport = delta * Real.log 0 = 0, because Real.log 0 = 0. So polytopeRoundedSupport ∅ delta rho = fun _ => rho. That function is smooth, its deriv and second deriv are 0, and the curvature radius smoothSupportCurvatureRadius is rho, which is positive by hrho. The statement is about deriv (smoothSupportCurve h) theta, and smoothSupportCurve_regular (which does not use hu) needs only ContDiff ℝ ∞ h and positive curvature radius. So the proof changes as follows. Do `rcases u.eq_empty_or_nonempty with rfl | hu`. In the nonempty case use the existing proof. In the empty case, `simp [polytopeRoundedSupport, polytopeSoftSupport, polytopeSoftPartition]` shows h is the constant function rho. Then contDiff_const gives smoothness, and the radius computes to rho + 0 = rho > 0 via deriv_const. Then apply smoothSupportCurve_regular. The other lemmas that take hu (contDiff_polytopeRoundedSupport, polytopeRoundedSupport_add_deriv_deriv_pos) are only needed in the nonempty branch. So hu can be deleted. I did not claim the same for hdelta, because for negative delta the result is unclear.

### [`QuadraticCarleson.packetPoint_abs_sub_right_ge`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/CounterexampleGeometry.lean#L68-L86) — `lean-pool-0135`

Snippet: `samples/lean-pool/lean-pool-0135.lean`

- `(hN : 100 ≤ N)` (theorem): Only used to get (k.toNat:ℝ)=k via paperBohrIndex_cast_toNat. The statement holds for all integers k: only (k:ℝ) ≤ k.toNat is needed (Int.self_le_toNat). With j ≥ k.toNat+1, the goal is j - kt - 1/2 ≤ |k+τ-j|, and |k+τ-j| ≥ j-k-τ ≥ j-kt-τ > j-kt-1/2 since τ<1/2. For k<0, kt=0 and it is still true (e.g. k=-5,j=1,τ=.3: 1/2 ≤ 5.7). Neither N nor 100 ≤ N is needed. Can be dropped alone or together with hk.
- `(hk : k ∈ paperBohrIndices N)` (theorem): Only used for the cast equation (k.toNat:ℝ)=k. The inequality is true for every integer k, using just (k:ℝ) ≤ k.toNat (Int.self_le_toNat) and the bound |x| ≥ -x with τ < 1/2; the case k ≤ 0 (kt = 0) is also fine. Can be dropped alone or together with hN (N would then no longer appear in the statement, but it is an implicit argument and could be removed too).

### [`NavierStokes.PhysicalCoordinateBounds.xLift_homogeneous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalCoordinateBounds.lean#L421-L426) — `lean-pool-0136`

Snippet: `samples/lean-pool/lean-pool-0136.lean`

- `(_hy : y ∈ positiveTime)` (theorem): The binder is named with an underscore and is never used. The proof is `dsimp only [xLift, dilation_apply]; rw [Real.rpow_zero, one_mul]; exact mul_div_mul_left _ _ hr.ne'`, and it only uses `hr`. `positiveTime` appears nowhere else in the statement, and `y` is still needed by the other binders and the conclusion. Deleting `_hy` therefore leaves the statement unchanged and the same proof still works, so the theorem remains true and provable without it.

### [`NavierStokes.TerminalStress.swirlCoefficient_contDiffAt`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalStress.lean#L412-L420) — `lean-pool-0158`

Snippet: `samples/lean-pool/lean-pool-0158.lean`

- `(hh1 : h < 1 / 2)` (theorem): hh1 is only used to apply SimilarityProfile.inner_smoothAt, flattening_contDiffAt and q_pos. These need it because q h p = SimilarityCoordinates.coordinateQ (2*h) (1-p.1, p.2.2). That is defined as `if 0 < a ∧ a < 1 ∧ 0 < p.1 then Classical.choose … else 1`, with a = 2*h. When h ≥ 1/2 we have a ≥ 1, so the `if` fails for every p and q h ≡ 1. The theorem stays true in that case. Then X h p = p.2.1 / 1 = p.2.1, which is smooth near p, and positive by hs. So log ∘ X h is smooth at p, and f ∘ log ∘ X h is C² by hf. physicalHeat C (1+h) is smooth at p using only hh (1 < 1+h) and ht. The sqrt factor is handled as before: 2*p.2.1 > 0 by hs. A proof splits on h < 1/2. If it holds, use the existing argument. If not, show `q h = fun _ => 1` by unfolding q and coordinateQ with `dif_neg`, then redo flattening_contDiffAt with that constant q. The rest of the proof is unchanged. The other hypotheses are not removable: hh is needed for 1 < 1+h in physicalHeat_contDiffAt, and ht and hs are needed for the heat term, the log argument and the sqrt.

### [`PDL.LoadedCluster.satDown_three_not_basic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/ClusterSatDown.lean#L575-L602) — `lean-pool-0171`

Snippet: `samples/lean-pool/lean-pool-0171.lean`

- `(hlen : next.length = (C.stepOfL Δ).length)` (theorem): hlen is used only in `have hi' : i < next.length := by omega`, where `i < (C.stepOfL Δ).length` comes from `hS.nonBasicStep`. Without hlen the theorem is still true and provable, because hlab already forces this. For that i with hi, `hlab i hi` gives `C.Q.labelAt (x ++ [i]) = some _`. Unfolding `QuasiTab.labelAt` and using `QuasiTab.atOpt_snoc` (PreInterpolant.lean:202) together with hx gives `(some (QNode .three Δ next)).bind (fun n => n.children[i]?)`, so `next[i]? ≠ none`. Hence `i < next.length`, by `List.getElem?_eq_none` by contradiction. Nothing else uses hlen. The statement never mentions it except as a hypothesis, and `next` is still fixed by hx. The conjunction in `iitp_three_not_basic` ranges over `next`, and only the chosen index i is used. Delete hlen and replace the omega step with this argument.

### [`NavierStokesAndEuler.SmoothCutoff.cutoff_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/ForMathlib/SmoothCutoff.lean#L86-L90) — `lean-pool-0181`

Snippet: `samples/lean-pool/lean-pool-0181.lean`

- `(hR : 0 < R)` (theorem): hR can be dropped. Since 0 ≤ ‖x‖ ≤ R, we get R ≥ 0. If R > 0, the existing proof works. If R = 0, then ‖x‖ ≤ 0 gives x = 0. So R⁻¹ • x = 0 • 0 = 0 (smul_zero), and cutoff E 0 0 = baseCutoff E 0 = 1 by baseCutoff_eq_one, because ‖0‖ = 0 ≤ 1. R < 0 is impossible because it contradicts ‖x‖ ≤ R. The statement therefore stays true without hR. A proof: apply baseCutoff_eq_one; rcases (norm_nonneg x).trans hx |>.eq_or_lt with h | h. In the case R = 0, x = 0 follows from norm_le_zero_iff and the goal is ‖R⁻¹ • x‖ ≤ 1 with x = 0, which simp closes. Otherwise use the existing argument with h : 0 < R.

### [`BooleanIsoperimetry.harper_macaulay_min`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L154-L176) — `lean-pool-0191`

Snippet: `samples/lean-pool/lean-pool-0191.lean`

- `(ha : a ≤ 2 ^ N)` (theorem): The statement stays true without `ha`. If a ≤ 2^N, the original proof applies, using `hb` or the case split on b. If a > 2^N, then H N a ≥ H N (2^N) = 2^N by `H_mono` and `H_full`. So max (H N a) b ≥ 2^N, and max (H N b) a ≥ a > 2^N. The RHS is therefore > 2^(N+1). The LHS satisfies H (N+1) (a+b) ≤ 2^(N+1) by `H_le_cube`, so the inequality holds. The junk case is harmless because `simplicialInitSeg` is `rank x < k`, which is the whole cube for large k. The proof becomes a case split on a ≤ 2^N, using the existing argument in one branch and this estimate in the other. The same applies to `hb`, so each hypothesis can be dropped on its own. Both can also be dropped together, because the cases a > 2^N, b > 2^N, and both ≤ 2^N are each covered.
- `(hb : b ≤ 2 ^ N)` (theorem): The statement stays true without `hb`. If b ≤ 2^N, use the original proof. If b > 2^N, then H N b ≥ H N (2^N) = 2^N by `H_mono` and `H_full`. So max (H N b) a ≥ 2^N, and max (H N a) b ≥ b > 2^N. The RHS is therefore > 2^(N+1), while the LHS is ≤ 2^(N+1) by `H_le_cube`. The proof is a case split on b ≤ 2^N, using the existing argument in one branch and this bound in the other. This is symmetric to `ha`. Both hypotheses can be dropped together by splitting on whether a or b exceeds 2^N.

### [`PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PebblingLean/UpperBoundParameters.lean#L2099-L2138) — `lean-pool-0205`

Snippet: `samples/lean-pool/lean-pool-0205.lean`

- `(hsmall : splitM K n < n)` (theorem): hsmall follows from hslack, so it can be dropped. By definition splitA K n = n - splitM K n (ℕ subtraction). Suppose ¬(splitM K n < n). Then splitA K n = 0, so (4/3)^splitA = 1 and hslack reads 1 ≤ loss n = ((n:ℝ)^2)⁻¹. For n = 0 this is 1 ≤ 0⁻¹ = 0, which is false. For n ≥ 2 we have loss n ≤ 1/4 < 1, which is false. So n = 1. But splitM K 1 = ⌈K * sqrt(1 * Real.log 1)⌉₊ = ⌈K * sqrt 0⌉₊ = ⌈0⌉₊ = 0 < 1, a contradiction. So the proof can start with `have hsmall : splitM K n < n := by by_contra h; ...` using this case analysis. The rest of the proof (recursiveCostBound_step hn hsmall, hsplit, etc.) is unchanged. The other two hypotheses are needed. hn is needed because for n < n0 the cost is 2^n * minPile n, not the recursive step. For example, K = 0, n = 25, n0 = 100 satisfies hsmall and hslack, but the inequality fails: the LHS is 2^30/(4/3)^25, which is huge, and the RHS is about 1.003. hslack is needed because the ceiling can exceed (1+2·loss)·(4/3)^a without it.

### [`AleksandrovDifferentiability.prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/AleksandrovDifferentiability/Analysis/GoodSet.lean#L97-L106) — `lean-pool-0218`

Snippet: `samples/lean-pool/lean-pool-0218.lean`

- `[SFinite ν]` (theorem): The statement only uses `μ.prod ν`, and `Measure.prod` takes no instance arguments. In Mathlib (Measure/Prod.lean, line 172) it is defined as `if SFinite ν then bind μ (fun x => map (Prod.mk x) ν) else 0`, so the junk value is `0` when `ν` is not s-finite. Without the hypothesis, the proof splits on `SFinite ν`. If `ν` is s-finite, run the current argument with `haveI`. If it is not, `μ.prod ν = 0`, so `μ.prod ν (s \ G) = 0` holds by unfolding `Measure.prod` with `if_neg`, i.e. `simp [Measure.prod, h]`. The theorem therefore stays true and provable without `[SFinite ν]`.

### [`TauCeti.DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_reducingSubspace`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/SinTheta/Natural/Reducing.lean#L496-L543) — `lean-pool-0223`

Snippet: `samples/lean-pool/lean-pool-0223.lean`

- `(hAdense : Dense (A.domain : Set ER))` (theorem): It follows from `hA : IsSelfAdjoint A`. Mathlib has `IsSelfAdjoint.dense_domain` (Mathlib/Analysis/InnerProductSpace/LinearPMap.lean, line 241). It needs `[CompleteSpace ER]`, which is available, and the library already uses it as `h.dense_domain`. The same star/adjoint structure is used here. The proof builds the record `P` with `A_dense := hA.dense_domain`. The statement is unchanged and the hypothesis is not mentioned elsewhere in it.
- `(hAclosed : A.IsClosed)` (theorem): It follows from `hA : IsSelfAdjoint A`. Mathlib has `IsSelfAdjoint.isClosed` (same file, line 340), which gives `A.IsClosed` from self-adjointness. The proof uses `A_closed := hA.isClosed`. The statement does not mention `hAclosed`.
- `(hA0dense : Dense (A0.domain : Set FR))` (theorem): It follows from `hA0 : IsSelfAdjoint A0` by `IsSelfAdjoint.dense_domain`, with `[CompleteSpace FR]` available. The proof uses `A₀_dense := hA0.dense_domain`. The statement does not mention `hA0dense`.
- `(hA0closed : A0.IsClosed)` (theorem): It follows from `hA0 : IsSelfAdjoint A0` by `IsSelfAdjoint.isClosed`. The proof uses `A₀_closed := hA0.isClosed`. The statement does not mention `hA0closed`. Each of these four hypotheses can be deleted on its own, and all four can be deleted together.

### [`CarlsonFunctions.SeveralComplexVariables.norm_sub_le_of_separately_analytic_bounded`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CarlsonFunctions/SeveralComplexVariables/LocallyBounded.lean#L67-L108) — `lean-pool-0237`

Snippet: `samples/lean-pool/lean-pool-0237.lean`

- `(hr : 0 < r)` (theorem): hr appears only in the proof, not in the conclusion. The statement stays true without it. If r < 0, then closedBall c r is empty, so hx is contradictory and the claim holds vacuously. If r = 0, then hx and hy give x = c and y = c, so y - x = 0. The left side is ‖f c - f c‖ = 0, and the right side is card ι * (M/0) * 0 = 0 (M/0 = 0 in Lean anyway). The inequality 0 ≤ 0 holds. For r > 0 the existing proof applies unchanged. A proof would start with `rcases lt_or_ge 0 r with hr | hr` and run the current proof in the first branch. In the second branch it would use `mem_closedBall`, `dist_nonneg` and `dist_le_zero` (or `Metric.closedBall_eq_empty`) to get x = c and y = c (or a contradiction), then `simp`.

### [`LeanPool.Besicovitch.sigma_mul_radius_div_two_le_diam_localAttachmentComponent`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Besicovitch/Rectifiability/ComponentDiameter.lean#L38-L191) — `lean-pool-0244`

Snippet: `samples/lean-pool/lean-pool-0244.lean`

- `(hsigma_one : sigma < 1)` (theorem): The only place the proof uses it is `hR_rho : sigma * rho / 2 < rho`, obtained by `nlinarith` from `sigma < 1` and `0 < rho`. The calls to `uniformDensitySet_ball_measure_gt` take only `hsigma` and `hsigma_gamma`. `openConvexHull_mem_badConvexSets` and `exists_isClopenWithin_between_connectedComponentIn_closedBall` do not take it either; the latter takes `hR_rho`, not `sigma < 1`. The hypothesis is not needed, because `hR_rho` already follows from `hannulus`. Take `w ∈ (ball z rho \ ball z (sigma*rho/2)) ∩ F`. If `rho ≤ sigma*rho/2`, then `Metric.ball_subset_ball` gives `ball z rho ⊆ ball z (sigma*rho/2)`. That contradicts `w ∈ ball z rho` and `w ∉ ball z (sigma*rho/2)`. Hence `sigma*rho/2 < rho` by `not_le`, and the rest of the proof goes through unchanged. So the theorem is still true and provable without `hsigma_one`. The change is to replace the `nlinarith` line with a short argument by contradiction using `hannulus`.

### [`CKN.norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Poincare/Lp.lean#L159-L202) — `lean-pool-0254`

Snippet: `samples/lean-pool/lean-pool-0254.lean`

- `[MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]` (theorem): The statement never uses this instance. It only mentions `(volume U).toReal`, `integralAverage U u` (defined as `average (volume.restrict U) u`) and set integrals, and none of these need it to elaborate. The hypothesis `hvol : 0 < (volume U).toReal` already implies `volume U ≠ ⊤`, because `ENNReal.toReal ⊤ = 0`. `volumeMeasureOn U` unfolds to `volumeOn U`, which is `volume.restrict U`, and its total mass is `volume U` (by `Measure.restrict_apply_univ`). So `IsFiniteMeasure (volumeMeasureOn U)` follows from `hvol`. The proof uses the instance only through `norm_sub_integralAverage_le_volumeAverage_integral_norm_sub`, which takes `[IsFiniteMeasure (volumeOn U)]`. After deleting the binder, the proof can start with `haveI : IsFiniteMeasure (volumeMeasureOn U) := ⟨by simpa [Measure.restrict_apply_univ, lt_top_iff_ne_top] using (ENNReal.toReal_pos_iff.mp hvol).2⟩`, or an equivalent short argument. The other ingredients are `norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment`, which has no measure hypotheses, and `integral_mono_ae`, which needs only the integrability facts `hleftInt` and `hsegment`. The statement stays true because the conclusion is the same, and the other hypotheses `hu`, `hvol` and `hsegment` are untouched.

### [`EGZ.CommonMeasure.final_mass_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ErdosGinzburgZiv/EGZ/Decomposition/CommonMeasure.lean#L109-L119) — `lean-pool-0276`

Snippet: `samples/lean-pool/lean-pool-0276.lean`

- `(hε : 0 < ε)` (theorem): The conclusion still holds when ε ≤ 0. Then ε/2 ≤ 0 and mass u P ≥ 0 by `mass_nonneg u hu P`, so the left side is ≤ 0. The right side satisfies 0 ≤ mass u Q, again by `mass_nonneg u hu Q`. When 0 < ε, the existing proof works unchanged. A proof would do `by_cases 0 < ε`. The first case uses the current term. The second case uses `mul_nonpos_of_nonpos_of_nonneg` (or nlinarith) together with `mass_nonneg`. `hu` is still available. This can be deleted on its own, and also together with hR.
- `(hR : 0 < R)` (theorem): The conclusion still holds when R ≤ 0. By `mass_weight_mono w u hle P` and hP, mass u P ≤ mass w P ≤ R ≤ 0. If ε ≥ 0, then ε/2 * mass u P ≤ 0 ≤ mass u Q, using `mass_nonneg u hu Q`. If ε < 0, then ε/2 * mass u P ≤ 0 because mass u P ≥ 0 by `mass_nonneg`. When R > 0, the existing proof works unchanged. A proof would do `by_cases 0 < R`. This can be deleted on its own, and also together with hε. In every case where either is dropped, the remaining sign facts still give LHS ≤ 0 ≤ RHS.

### [`eigenvector_constant_sign`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SpectralPositivity/Operator/JentzschProof.lean#L332-L387) — `lean-pool-0280`

Snippet: `samples/lean-pool/lean-pool-0280.lean`

- `(hT_compact : IsCompactOperator T)` (theorem): Compactness is never used. hT_compact appears only as an argument to `abs_eigenvector_of_top_eigenvector`, and that lemma names it `_hT_compact` and never uses it. Its proof uses only self-adjointness, positivity preservation, the eigen-equation, the upper bound `hlam₀_top`, and `eq_smul_self_of_isLocalExtrOn`, which needs only `IsSelfAdjoint T`. The rest of `eigenvector_constant_sign` uses `ground_state_strictly_positive`, which has no compactness hypothesis. So the theorem is true and provable without `hT_compact`. To remove it, drop the unused `_hT_compact` binder from `abs_eigenvector_of_top_eigenvector`, or copy its proof inline, and delete the argument at the call site. No degenerate cases arise.

### [`QuadraticCarleson.annularQuadraticKernel_correlation_le_ordered`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/QuadraticFixedHeightAveragingCorrelation.lean#L49-L127) — `lean-pool-0281`

Snippet: `samples/lean-pool/lean-pool-0281.lean`

- `(hD : 0 ≤ D)` (theorem): It follows from the other hypotheses. hab 0 gives ‖a 0‖ ≤ D / R. The norm is nonnegative, so 0 ≤ D / R. Since hR : 0 < R, this gives 0 ≤ D (e.g. `(div_nonneg_iff ...)` or `by_contra` plus `div_neg_of_neg_of_pos`). In the proof, hD is only used implicitly by `positivity` (nonnegativity of D / S and D ^ 2 / (R * S)). The goals `0 ≤ D / S` and similar can be obtained from `(norm_nonneg _).trans (hbb 0)`. P ≥ 0 does not need hD because D ^ 2 is a square. So the statement stays true and provable without hD.
- `(hH : 0 < H)` (theorem): It follows from hdecay : 1 ≤ H * u ^ 5 and hu : 0 < u. We have 0 < 1 ≤ H * u ^ 5 and u ^ 5 > 0. If H ≤ 0 then H * u ^ 5 ≤ 0, a contradiction, so H > 0. This can be done with `pos_of_mul_pos_...` or `by_contra; nlinarith [pow_pos hu 5]`. The only use of hH in the proof is passing it to norm_integral_quadraticTTStar_fixed_height_supported, and the derived fact can be passed there instead. The statement is unchanged, so hH can be deleted.

### [`AVenhance.Infra.Section3.ChiMKCorrector.chiMK_spaceLap_three_active`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section3/ChiMKCorrector.lean#L159-L209) — `lean-pool-0282`

Snippet: `samples/lean-pool/lean-pool-0282.lean`

- `(hk : k % 4 = 3)` (theorem): The statement is still true for every k, because the 0-component of chiMK vanishes identically unless k % 4 = 3. By definition chiMK κ m k t x = (-(corrTime ..)) • uShear β Λ m k x. Look at uShear x 0 in each case. If k % 4 = 1, uShear is ![0, ...], so its 0-component is 0. If k % 4 = 3, it is -(2π a ε cos(2π x 1/ε)), which is the active case. Otherwise uShear is 0. So when ¬(k % 4 = 3), the function y ↦ chiMK κ m k t y 0 is identically 0. Then the existing lemma ChiMKCorrector.chiMK_spaceLap_of_zero_component, which appears earlier in the same file with the hypothesis hzero : (fun y => I.chiMK κ m k t y j) = fun _ => 0, gives exactly the stated conclusion (both sides are 0). The proof is by_cases hk : k % 4 = 3. The positive case is the current proof, with hk as a local hypothesis. The negative case is: apply chiMK_spaceLap_of_zero_component with j = 0, proving hzero by funext y; simp [Ingredients.chiMK, uShear], then split on k % 4 = 1 and use hk. Nothing in the statement mentions hk, so removing it does not break elaboration.

### [`Malliavin.memLp_mderiv_cylinder_expGrowth`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/CylindricalGrowth.lean#L488-L496) — `lean-pool-0295`

Snippet: `samples/lean-pool/lean-pool-0295.lean`

- `(hC : 0 ≤ C)` (theorem): It follows from hfg'. Specialise hfg' at y = 0 (the zero vector of Fin n → ℝ, which exists even for n = 0). This gives 0 ≤ ‖fderiv ℝ f 0‖ ≤ C * exp (c * ‖0‖) = C * exp 0 = C. The proof can start with `have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hfg' 0)` and then proceed unchanged. The statement is therefore still true and provable without hC. This can be deleted together with hc, because the argument below only needs hfg'.
- `(hc : 0 ≤ c)` (theorem): The theorem stays true without it. The hypothesis is only used to apply expGrowth_coord_le, which needs 0 ≤ c to compare exp (c * ‖fun i ↦ L i x‖) with exp (c * ((∑ ‖L i‖) * ‖x‖)). If c < 0, then exp (c * ‖y‖) ≤ 1 for all y. With C ≥ 0 (derived from hfg' as above), hfg' gives ‖fderiv ℝ f y‖ ≤ C * exp (c * ‖y‖) ≤ C = C * exp (0 * ‖y‖). So the same argument works with c' = max c 0 ≥ 0 in place of c: hfg' is weakened to C * exp (c' * ‖y‖) using C ≥ 0 and monotonicity of exp. Then apply memLp_mderiv_cylinder_of_dominated with ψ := C * exp (c' * ((∑ ‖L i‖) * ‖x‖)), expGrowth_coord_le (with hc' : 0 ≤ c') and integrable_expGrowth_sq μ C c' _. The conclusion does not mention c, so it is unchanged.

### [`Malliavin.BrownianIteratedConstruction.wickPurePowerMixedInnerIdentity_of_generated`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/BrownianPurePowerDuality.lean#L393-L402) — `lean-pool-0298`

Snippet: `samples/lean-pool/lean-pool-0298.lean`

- `(hsm : ∀ t, StronglyMeasurable (B t))` (theorem): The hypothesis `generated : IsWienerGenerated B` already implies it. `Malliavin.IsWienerGenerated.measurable` (IteratedIntegral.lean line 533) gives `Measurable (B t)` for every `t` from `generated`, with no other assumptions. Since `B t : W → ℝ` and ℝ is second countable, metrizable and has the Borel σ-algebra, `Measurable.stronglyMeasurable` turns this into `StronglyMeasurable (B t)`. So the proof can start with `have hsm : ∀ t, StronglyMeasurable (B t) := fun t => (generated.measurable t).stronglyMeasurable` and then proceed unchanged. The statement does not otherwise mention `hsm`, so deleting the binder leaves the statement as it was. It is true because `hsm` is derivable from `generated`.


## FLT (Anthropic) (52 flagged)

### [`P2MW.S_ModularCurve_full_eq_adjoin_primes.ModularCurve.W1.roots_prime_at_slot_roots_nodup`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_full_eq_adjoin_primes.lean#L306-L312) — `flt-anthropic-0001`

Snippet: `samples/flt-anthropic/flt-anthropic-0001.lean`

- `(hζ : IsPrimitiveRoot (ζ : K) N)` (theorem): The conclusion (roots of `data.Φ.map (eval₂RingHom … (qExpand K (p*e) (qTwist (u^p) (coeffEmb K jq))))` are `Nodup`) mentions neither `N`, `ζ` nor `hζ`. Only the proof uses them, to rewrite the roots via `roots_prime_at_slot` into an explicit multiset. The statement is still true without `hζ`. The polynomial has p+1 distinct roots over an algebraic closure. Take K' = AlgebraicClosure K, which has an `Algebra ℚ` structure and a primitive p-th root of unity ζ'. Apply the existing theorem over K' with N := p, `hpN := dvd_rfl` and u' := image of u. Then transfer back along the injective ring map K((q)) → K'((q)). The library exports the commutation lemmas `coeffMap_qExpand` and `coeffMap_injective` for this. Injectivity gives `Polynomial.le_rootMultiplicity_map`, so rootMultiplicity a f ≤ rootMultiplicity (ι a) (f.map ι) ≤ 1, using f.map ι ≠ 0 (Φ is monic). That gives `Nodup`. Without `hζ` the roots need not lie in K((q)), but nodup of the root multiset is unaffected, because it is a statement about multiplicities. Not a degenerate case: with K = ℚ and p = 3 no primitive cube root exists, and the claim is still true by the base-change argument. Only this binder is removed; the other arguments stay.
- `(hpN : p ∣ N)` (theorem): `p ∣ N` appears only in the hypotheses and in the proof, not in the conclusion, which depends only on K, p, data, e and u. The result is true whatever N, ζ are. The same base-change argument works: pass to K' = AlgebraicClosure K, pick a primitive p-th root ζ' there, and apply the existing theorem with N := p and `hpN := dvd_rfl`. Then descend nodup of the roots along the injective map K((q)) → K'((q)), using `coeffMap_qExpand`, `coeffMap_injective` and `Polynomial.le_rootMultiplicity_map`. The hypothesis is therefore redundant. It could be deleted on its own, and also together with `hζ` (then N and ζ become unused, and the theorem is provable by the same route). Each can be removed separately.

### [`P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.C2idemCore.IdempotentOrbit.exists_idempotent_orbit_or_isField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.lean#L172-L278) — `flt-anthropic-0014`

Snippet: `samples/flt-anthropic/flt-anthropic-0014.lean`

- `[Finite ι]` (theorem): I believe the statement is still true without `Finite ι`, but the existing proof would need rewriting, and I could not run Lean to check. The proof only uses it through `Fintype.ofFinite ι` and the helper `exists_indexMap_of_iterate_eq`. The mathematical argument for an arbitrary `ι` is as follows. The empty case is already handled. Otherwise let `t = conj φ s`, an automorphism of `Π i, F i` with `t^n = id`.

1. `t` sends each `ind {j}` to some `ind {j'}`. The image `t(ind {j})` is a nonzero idempotent, so it is `ind A` for a nonempty set `A` of coordinates. Suppose `A` had two elements. Then `ind A` splits as `ind {a} + ind (A\{a})`, two nonzero orthogonal idempotents. Applying `t⁻¹ = t^(n-1)` splits `ind {j}` into two nonzero orthogonal idempotents. That is impossible, because any idempotent `u` below `ind {j}` is supported on `{j}` and the coordinate field has only the idempotents 0 and 1.

2. So `t(ind {j}) = ind {ψ j}` for some `ψ j`, and `ψ^n = id` because `t^n = id`.

3. Take any `j₀`. Its `ψ`-orbit `O` is finite, with at most `n` elements, and is `ψ`-invariant.

4. Then `ind O` (a sum of finitely many `ind {j}`) is fixed by `t`. So `φ.symm (ind O)` is an idempotent fixed by `s`. By `hfix` and the proof's `hfix01`, it is 0 or 1. It is nonzero, so it is 1, which gives `O = univ`.

5. Hence `ι` is finite.

The rest of the existing proof then runs unchanged, with `Finite ι` and the Fintype structure derived locally. `hn` is not redundant. For `n = 4`, `R = k × k` and `s` the swap, `hs` and `hfix` hold, but the conclusion fails, so primality is needed. The remaining binders (`φ`, `s`, `hn`, `hs`, `f`, `hfix`) are all used or needed for the statement.

### [`P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6.comp_heckeDiag_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.lean#L664-L678) — `flt-anthropic-0018`

Snippet: `samples/flt-anthropic/flt-anthropic-0018.lean`

- `(hp : p ≠ 0)` (theorem): `heckeDiagMatrix` is defined in Definitions/Def_ModularForm_HeckeOperator.lean as `if hp : p = 0 then 1 else upperTriangularGL p 0 1 _`. For p = 0 it is therefore the identity matrix, and `1 • τ = τ`. The function in the conclusion is then `fun τ => F τ`, which is `F` and is nonzero by `hF`. So the statement is true for p = 0 as well. For a proof without `hp`, do `by_cases h : p = 0`. In the case p = 0, `subst h; simpa [ModularForm.heckeDiagMatrix] using hF` works, since the `dif_pos` branch gives `1`, then `one_smul` and eta-reduction. In the case p ≠ 0, use the existing proof. Only the hypothesis is deleted and the statement is otherwise unchanged.

### [`P2MW.S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.Blk176Arith.not_cube_dvd_mul_prod_filter`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.lean#L147-L182) — `flt-anthropic-0038`

Snippet: `samples/flt-anthropic/flt-anthropic-0038.lean`

- `(hN0 : N ≠ 0)` (theorem): hN0 follows from hN3. If N = 0, then hN3 2 Nat.prime_two says ¬ 2^3 ∣ 0, which is false by dvd_zero, so hN3 would be contradictory. The statement therefore remains true without hN0. In the proof, replace the hypothesis with `have hN0 : N ≠ 0 := by rintro rfl; exact hN3 2 Nat.prime_two (dvd_zero _)` at the start; the rest of the proof is unchanged.

### [`P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.P2mS17LB.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.lean#L49-L111) — `flt-anthropic-0046`

Snippet: `samples/flt-anthropic/flt-anthropic-0046.lean`

- `(hn : 0 < n)` (theorem): hn follows from the other hypotheses. If n = 0, then hqn : ¬ (q:ℕ) ∣ 0 is false, because every number divides 0. So hqn alone gives n ≠ 0, and hence 0 < n. (hα also rules out n = 0: it would say 1 = (q:ℕ) in the algebraic closure, but q is prime.) The statement stays true after deleting hn. The proof only needs to start with `have hn : 0 < n := Nat.pos_of_ne_zero (fun h => hqn (h ▸ dvd_zero _))`. The rest of the proof is unchanged, since it uses hn only through this local fact (for example in `Nat.mul_pos hn hd`, `hn.ne'`, and `zero_pow hn.ne'`).

### [`P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.PLCDSol.exists_gamma0_apply_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.lean#L883-L889) — `flt-anthropic-0048`

Snippet: `samples/flt-anthropic/flt-anthropic-0048.lean`

- `[NeZero M]` (variable): The statement only uses `(ZMod M)ˣ`, `CongruenceSubgroup.Gamma0 M` and `SL(2, ℤ)`, none of which needs `NeZero M`. The proof currently uses `CohCarrier.gamma0Units_surjective`, which does take `[NeZero M]` (Def_CohCarrier_Inst.lean:39), but the hypothesis can still be dropped. Split on `M = 0`. If `M ≠ 0`, use `haveI : NeZero M := ⟨hM⟩` and run the existing proof. If `M = 0`, then `ZMod 0 = ℤ`, so the unit `d` is `±1`, and `Gamma0 0` is the set of matrices with `c = 0` (the bottom-left entry, cast to `ZMod 0`). The matrix `!![d, 0; 0, d]` has determinant `d² = 1` and lies in `Gamma0 0`. Its (0,0) entry casts to `d`, so the claim holds. `H` is not an argument: it is not mentioned in the statement and is not instance-implicit.

### [`P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.CohCarrier.gammaH_inf_gamma0_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.lean#L104-L128) — `flt-anthropic-0049`

Snippet: `samples/flt-anthropic/flt-anthropic-0049.lean`

- `[NeZero N]` (theorem): The statement never needs it. `CohCarrier.GammaH` and `gamma0Units` (Definitions/Def_CohCarrier_Level.lean) take an arbitrary `M : ℕ`, and Mathlib's `Gamma0`, `Gamma0Map` and `ZMod.unitsMap` take no `NeZero` assumption. The proof only uses `mem_GammaH_iff`, `Gamma0_mem`, `ZMod.castHom` (which needs `CharP (ZMod N) N`, available for every N), `map_intCast` and `ZMod.unitsMap_def`. It calls no lemma that needs `NeZero`. The statement is true for all N and ℓ, including N = 0 and ℓ = 0, because the proof never uses nonzeroness. `NeZero (N*ℓ)` already implies `NeZero N`, and neither is needed. Both instances can be deleted together.
- `[NeZero (N * ℓ)]` (theorem): The statement never needs it. `GammaH (N*ℓ) …`, `Gamma0 (N*ℓ)` and `ZMod.unitsMap (dvd_mul_right N ℓ)` are all defined for arbitrary natural numbers with no `NeZero` assumption. The proof only does a membership computation with casts through `ZMod.castHom`, which is a ring hom for any divisibility `N ∣ N*ℓ`. It never uses finiteness of `ZMod (N*ℓ)`. Deleting this hypothesis leaves the statement true and the proof unchanged. It can be deleted together with `[NeZero N]`.

### [`P2MW.S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.ModularCurve.CupPairing.Shapiro.b_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_CupPairing_exists_isParabolicHom_eq_sub_of_forall_finsum_eq_zero.lean#L287-L288) — `flt-anthropic-0052`

Snippet: `samples/flt-anthropic/flt-anthropic-0052.lean`

- `[Γ.FiniteIndex]` (variable): This instance is taken automatically: it is instance-implicit and its only dependency, Γ, is an argument. Nothing in the statement or the math needs it. The statement mentions only `P : Potentials Γ f`, `P.b`, `phi P` and `Additive.ofMul γ`. `Potentials` is a structure, and structures keep only the section variables their fields use. Its fields use Γ and f (through `cfun Γ f`) and not the instance. `cfun` is a def whose header and body do not use the instance either. The elaborator drops unused section variables for defs, so `cfun` takes no instance, and neither does `phi`. So the statement elaborates without `[Γ.FiniteIndex]`.

The statement is also true without it. `P.hab` gives `cfun Γ f g = P.b g - P.a g`. `cfun Γ f (g*γ) = cfun Γ f g` for γ ∈ Γ (the proof of `cfun_mul_mem` is `QuotientGroup.eq`, with no finiteness). `P.hb` and `P.ha` are the invariance properties of b and a. `eq_apply_one_of_S_U` is a general lemma about functions on SL(2,ℤ) and needs no hypotheses on Γ. So the chain `a_mul_sub_eq` → `b_mul_sub_eq` → `b_mul` never uses finite index. Those intermediate lemmas also pick up the instance only via the same automatic inclusion, and the instance is not used in any of their proofs. To delete it from `b_mul` you would have to make the same deletion in `cfun_mul_mem`, `a_mul_sub_eq` and `b_mul_sub_eq` (for example with `omit [Γ.FiniteIndex] in`). The proofs do not change otherwise.

### [`TateCurve.pointX_inv_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_TateCurve_XMultStructure.lean#L171-L175) — `flt-anthropic-0057`

Snippet: `samples/flt-anthropic/flt-anthropic-0057.lean`

- `(hu0 : u ≠ 0)` (theorem): If u = 0 then u⁻¹ * v = 0 * v = 0 and u * v⁻¹ = 0 * v⁻¹ = 0 (using inv_zero). Both sides are then pointX q 0, so the claim holds by rfl or simp. If u ≠ 0 the existing proof works unchanged. So the proof is `by_cases hu0 : u = 0; · simp [hu0]; · (existing proof)`. The hypothesis is also redundant in the called lemma, because OffLattice q 0 is trivially true. It can be removed on its own. It can also be removed together with hv0, since the case split is only on whether u or v is 0.
- `(hv0 : v ≠ 0)` (theorem): If v = 0 then u⁻¹ * v = 0 and u * v⁻¹ = u * 0 = 0 (using inv_zero and mul_zero). Both sides are then pointX q 0, so the claim holds by simp. If v ≠ 0 the existing proof works unchanged. So a case split on v = 0 removes the need for hv0. It can be removed on its own, and also together with hu0.

### [`P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.Nat.not_mem_placesOf_of_mem_placesOf_of_coprime`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.lean#L72-L74) — `flt-anthropic-0058`

Snippet: `samples/flt-anthropic/flt-anthropic-0058.lean`

- `(hℓ : ℓ ≠ 0)` (theorem): placesOf is defined as `if h : span {(ℓ : 𝓞 ℚ)} = ⊥ then ∅ else ...`. For ℓ = 0 we have span {0} = ⊥, so placesOf 0 = ∅. Then `hv : v ∈ placesOf 0` is false, and the conclusion holds vacuously. Proof: `by_cases hℓ : ℓ = 0`. In the zero case, `subst hℓ`, unfold placesOf, rewrite with `dif_pos` (using `Ideal.span_singleton_eq_bot` and `Nat.cast_zero`), and close the goal with `simp at hv`. Otherwise use the existing proof. The other hypotheses stay unchanged.
- `(hℓ' : ℓ' ≠ 0)` (theorem): For ℓ' = 0, placesOf 0 = ∅ because span {0} = ⊥ makes the `dif_pos` branch fire. So `v ∉ placesOf 0` holds trivially. Proof: `by_cases hℓ' : ℓ' = 0`. In the zero case, unfold placesOf, rewrite with `dif_pos`, and close the goal with `simp`. Otherwise use the existing proof. This is independent of hℓ. Each of hℓ and hℓ' can be removed on its own, and both can be removed together by splitting on each.

### [`P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.lean#L843-L876) — `flt-anthropic-0059`

Snippet: `samples/flt-anthropic/flt-anthropic-0059.lean`

- `(hn : ‖n‖ = 1)` (theorem): hn follows from hm except when m = 0. Here q = absNorm v ≥ 2.

Case m ≥ 1. Then ‖1 - n‖ = q^(-m) < 1. The ultrametric inequality then gives ‖n‖ = 1. So hn is derivable and the existing proof goes through unchanged.

Case m = 0. Then ‖1 - n‖ = 1, so ‖n‖ ≤ 1. The target index is q^(min s 0) = 1. This is the only case where hn is not implied.

If ‖n‖ = 1, the existing proof works.

Otherwise ‖n‖ < 1; n = 0 is allowed. Then hc gives ∏ θ^i c = n with norm < 1. The proof's own lemmas show v(θ^i c) = v(c): write c = algebraMap x * unit via exists_eq_algebraMap_mul_unit, then use v_algebraMap and v_theta_eq_one. Hence v(c)^d < 1, where d = finrank ≥ 2 by hprime. So v(c) < 1, and in particular c ∈ O_w. The case c = 0 is included, since v(c) = 0.

Now take x ∉ O_w. The same decomposition gives v(θx) = v(x) > 1. Also v(cx) < v(x). So v(θx - cx) = v(x) > 1, and x is not in comap(θ - mulLeft c) O_w. Elements of O_w are in that comap, because θ and mulLeft c preserve O_w (theta_mem). So comap(θ - mulLeft c) O_w = O_w.

Then {x ∈ O_w | ϖ^s x ∈ O_w} = O_w, since ‖ϖ‖ < 1. The intersection is therefore O_w and its relIndex in O_w is 1 = q^0. This matches the claim.

So the statement stays true after deleting hn. The proof needs an extra case split on m = 0 and ‖n‖ < 1, plus the short argument above. In the main case, ‖n‖ = 1 is obtained from hm. hn is used in the current proof only to get hn1, which feeds v_c_eq_one.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L610-L612) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- `[CharZero L]` (variable): The statement only needs `L` and `[Field L]`, which are needed to form `LaurentSeries L` and `algebraMap L (LaurentSeries L)`. `CharZero L` is instance-implicit and mentions only `L`, so it is pulled in as an argument. The proof is `rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]`. The lemma `ModularCurve.algebraMap_laurentSeries_eq_single` (Definitions/Def_ModularCurve_LaurentCoeff.lean, line 66) is stated under only `variable (L : Type*) [Field L]`, so it needs no characteristic assumption. `HahnSeries.C_apply` is a general lemma about the ring hom `C`. So the theorem holds and is provable for every field `L`, and `CharZero L` can be removed with `omit [CharZero L] in`.

### [`P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.W8O.ramificationIndex_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.lean#L169-L198) — `flt-anthropic-0064`

Snippet: `samples/flt-anthropic/flt-anthropic-0064.lean`

- `[CharP M p]` (variable): The statement `w.ramificationIndex M = p ^ r` does not mention `CharP M p`. Neither does the type of `hrange`, which only uses `algebraMap M E` and `iterateFrobenius E p r`, so only `CharP E p` is needed there. The hypothesis is used only inside the proof, where `theta` (via `IsPurelyInseparable.iterateFrobenius`) needs an `ExpChar M p` instance. That instance is implied by the other hypotheses. `algebraMap M E : M →+* E` is injective because `M` is a field. `RingHom.charP (algebraMap M E) (algebraMap M E).injective p` in Mathlib/Algebra/CharP/Algebra.lean then gives `CharP M p` from `CharP E p`. Alternatively, `RingHom.charP_iff_charP` gives the same, since `M` is a division ring and `E` is nontrivial. Starting the proof with `haveI : CharP M p := (algebraMap M E).charP (algebraMap M E).injective p` makes the rest of the proof go through unchanged. The theorem therefore stays true and provable without `[CharP M p]`. The degenerate cases do not matter, since `Fact p.Prime` is kept.

### [`P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.lean#L2414-L2438) — `flt-anthropic-0066`

Snippet: `samples/flt-anthropic/flt-anthropic-0066.lean`

- `(ha2 : a ^ (q ^ 2) = a)` (theorem): The hypothesis ha2 does not appear in the conclusion or in any other binder. The proof never uses it. After `subst hθ` the proof finishes with `exact ModularCurve.C4b.core θ f h₁ h₁F h₁0 a ha hsupp`, and that call is not given ha2. The proof therefore compiles unchanged with ha2 removed, so the theorem stays true and provable without it. I did not open the source of ModularCurve.C4b.core. The call shown elaborates without ha2, which is enough.

### [`P2MW.S_CohCarrier_isEis_kernel_pair_of_prime.CohCarrier.IsEisKernelPairPrime.exists_crt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_isEis_kernel_pair_of_prime.lean#L359-L443) — `flt-anthropic-0072`

Snippet: `samples/flt-anthropic/flt-anthropic-0072.lean`

- `[NeZero P]` (theorem): `mapN n` is the abbrev `Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))`, and the statement needs no `NeZero`. Without `[NeZero P]` the statement is still true. Coprimality of `P` and `M₁` with `P = 0` forces `M₁ = 1`. Then `g₁ := g` works, because `mapN 1 g₁ = 1` holds as `ZMod 1` is trivial, so `SL(2, ZMod 1)` is a subsingleton. If `P ≠ 0`, `NeZero P` is derivable (`⟨h⟩`), and the existing proof goes through unchanged. The proof only uses `NeZero P` to build `NeZero (P*M₁)` for `ModularCurve.surjective_specialLinearGroup_map_zmod`, so the proof needs this one case split. `[NeZero M₁]` can be kept while `[NeZero P]` is deleted.
- `[NeZero M₁]` (theorem): The statement does not need `NeZero M₁` to elaborate, since `mapN` takes any `ℕ`. It is still true without it. `M₁ = 0` together with `Nat.Coprime P 0` forces `P = 1`. Take `g₁ := 1`. Then `mapN 1 1 = mapN 1 g` because `SL(2, ZMod 1)` is a subsingleton, and `mapN 0 1 = 1` by `map_one`. If `M₁ ≠ 0`, `NeZero M₁` is derivable and the existing proof works. The proof only needs it for `NeZero (P*M₁)` in the surjectivity lemma. `[NeZero P]` can be kept while `[NeZero M₁]` is deleted. Both can in fact be deleted together, since `P = M₁ = 0` is not coprime. Each one is deletable on its own.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.K45VolB3.iterate_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.lean#L218-L220) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- `[NumberField L]` (variable): `[NumberField L]` is a section variable that is taken because `L` appears in the statement. Nothing in the statement or proof uses it. `AutomorphicForm.sigmaTensor K L A σ` is defined in a section that assumes only `[Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]`. The ring structure on `L ⊗[K] Kv` needs only those instances. `Kv` needs `NumberField K` for `IsDedekindDomain (𝓞 K)`, but nothing needs `NumberField L`. The proof rewrites with the local `sigmaTensor_pow`, which is stated under the same minimal assumptions, and then applies `map_mul` to the ring hom `sigmaTensor`. Neither step uses `NumberField L`. The statement is true without it, so it can be removed with `omit [NumberField L] in`, in addition to the existing `omit [IsGalois K L]`.

### [`P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD.pairF_res_cores_normal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_index_Gamma_four.lean#L5591-L5659) — `flt-anthropic-0095`

Snippet: `samples/flt-anthropic/flt-anthropic-0095.lean`

- `[Γ'.FiniteIndex]` (theorem): The statement never needs this instance. `cores hΦΓ` takes `[Φ.FiniteIndex]` (the smaller subgroup), `res` takes no finiteness instance, and `pairF Φ` takes only the Φ-instances. `Γ'` appears only as a type. It also follows from the other hypotheses: `hΦΓ : Φ ≤ Γ'` and `[Φ.FiniteIndex]` give `Subgroup.finiteIndex_of_le hΦΓ : Γ'.FiniteIndex` (Mathlib/GroupTheory/Index.lean). The proof never uses it directly either. `Fintype (Γ' ⧸ K)` comes from `Finite`, where `K = Φ.subgroupOf Γ'` has finite index because Φ does. If an instance is still needed, `haveI := Subgroup.finiteIndex_of_le hΦΓ` supplies it. So deleting the binder leaves the statement true and provable.

### [`P2MW.S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.lean#L99-L202) — `flt-anthropic-0099`

Snippet: `samples/flt-anthropic/flt-anthropic-0099.lean`

- `(hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)` (theorem): hcover is not mentioned in any later binder or in the conclusion. The proof never refers to it. It uses explicit `exact` and `rw` steps, with no `assumption` or `simp [*]`. The proof builds the finite bad set from the finiteness of `pullback i₁.1 i₂.1` (via hn, hn0) and from the nonempty open set U (via hne₁), then applies `Pic0.mem_closure_mk_single_sub_single_of_notMem`. The statement is therefore provable unchanged without hcover.
- `(hred : IsReduced (pullback i₁.1 i₂.1))` (theorem): hred is a plain hypothesis, not an instance. It appears nowhere else in the statement, and the proof does not use it. Finiteness of the pullback comes from hn and hn0. The statement is provable as is without hred.
- `(hM : 5 ≤ M)` (theorem): hM is not mentioned by any other binder or by the conclusion, and the proof never uses it. Only `[NeZero M]` is needed for `igusaFunctionFieldX1C k M w` to elaborate, and that stays.
- `(hpM : ¬ p ∣ M)` (theorem): hpM is not referenced by the statement or the proof. The proof only uses the structure of Mdl₁, e₁, c₁, i₁ and the finiteness facts.
- `(hζ : IsPrimitiveRoot ζ p)` (theorem): hζ is unused in the proof and not mentioned in the statement. ζ appears only in the hypotheses hζ and hζA, so deleting these hypotheses leaves the rest of the statement unchanged.
- `(hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))` (theorem): hK is a plain equation hypothesis. K is a variable in the statement, so deleting hK does not break elaboration. The proof never rewrites with it or uses it, and the argument is generic in K.
- `(hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)` (theorem): hj is a plain hypothesis on j. It is not used in the proof and not needed to state the conclusion, since j is still a variable. The proof is generic in j.
- `(hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)` (theorem): hAp is a plain hypothesis that is not used in the proof or mentioned in the statement.
- `(hζA : ∃ z : A, algebraMap A L z = ζ)` (theorem): hζA is a plain hypothesis that is not used in the proof or mentioned in the statement.

### [`P2MW.S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.lean#L32-L223) — `flt-anthropic-0121`

Snippet: `samples/flt-anthropic/flt-anthropic-0121.lean`

- `(hθ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), θ t = θ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))` (theorem): The proof never refers to hθ. The χ-points are built from χ i, the maps π, hΨ, hu and the lemma exists_points_jointly_injective_of_charpoly_frobenius_eq_of_isAbsolutelyIrreducible. That lemma is applied to θ' and the hypotheses on ρbar, and it does not take hθ. The remaining steps use hΨ, hres (via isLocalHom_and_residue_apply_pi for θ'), hu, hdich and hθ'U. θ appears in the statement only through the types heckeLocal ... θ (of Ψ, u, hΨ and hu), which still elaborate without hθ. Deleting hθ therefore leaves the statement unchanged and the same proof compiles. The only tactic that could use a hypothesis silently is `congr 1`, and it closes a goal that holds by proof irrelevance.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.M4aD2Skeleton.zetaIntegral_eq_setIntegral_theta'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.lean#L6363-L6392) — `flt-anthropic-0122`

Snippet: `samples/flt-anthropic/flt-anthropic-0122.lean`

- `(hD'm : MeasurableSet D')` (theorem): The only use of hD'm is in `MeasureTheory.setIntegral_congr_fun hD'm ...`. Mathlib's `MeasureTheory.IsFundamentalDomain` (the one used here, with `integral_eq_setIntegral_tsum_smul` taking `hD : IsFundamentalDomain G D μ`) has a field `nullMeasurableSet : NullMeasurableSet s μ`, so `hD'.nullMeasurableSet` is available. Mathlib has `MeasureTheory.setIntegral_congr_fun₀ (hs : NullMeasurableSet s μ) (h : EqOn f g s)`, which gives the same conclusion. The pointwise equality `EqOn` on D' is exactly what the proof already supplies. So the theorem is unchanged without hD'm: replace the `refine setIntegral_congr_fun hD'm ...` step by `setIntegral_congr_fun₀ hD'.nullMeasurableSet ...`. Nothing else in the proof or statement mentions hD'm. The other hypotheses (hχc, hχu, hs, hf, hχF, Haar) are used for integrability and the translation invariance of χ.

### [`P2MW.S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.NumberField.AdelicFourier.GodementSiegelEstimate.real_bound`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.lean#L337-L423) — `flt-anthropic-0123`

Snippet: `samples/flt-anthropic/flt-anthropic-0123.lean`

- `(hC : 0 ≤ C)` (theorem): The statement stays true without hC. Case C < 0: take B = 0. Then the right side is 0. On the left, C is negative, and (1+(rα)⁻¹²), (1+(rδ)⁻¹²) are positive. The sum of the two mins is nonnegative, because each min is of 1 and a nonnegative power. So the left side is ≤ 0 and the bound holds. Case C ≥ 0: the existing proof applies unchanged. It uses hC only in `positivity` for 0 ≤ B and in `gcongr`, and both are available in this case. So the proof just needs a `by_cases` or `rcases lt_or_ge C 0` on C. Equivalently, apply the existing argument to max C 0. The other hypotheses hc and hD cannot be dropped. Without hc, take c ≤ 0, so c ≤ H is vacuous. Then α → 0 with δ = D/α makes the left side blow up like (rα)⁻² while the right side stays bounded. Without hD, D ≤ αδ is vacuous, and the same blow-up occurs.

### [`P2MW.S_TateCurve_ks17_D3_exports.TateCurve.sum_mul_Fz_Fz_eq_sum_lines_nat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_ks17_D3_exports.lean#L108-L111) — `flt-anthropic-0124`

Snippet: `samples/flt-anthropic/flt-anthropic-0124.lean`

- `[IsUltrametricDist K]` (theorem): The statement is purely algebraic. `Fz u a = u^a + u^(-a) - 2` is defined for any `Field K`, and `Fz_zero : Fz u 0 = 0` holds. For x ∈ S with 0 ≤ g x, h x ≤ N, the terms with g x = 0 or h x = 0 vanish. The remaining terms are regrouped by the pair (g x, h x) ∈ Icc 1 N × Icc 1 N using `Finset.sum_fiberwise`-style regrouping and `Finset.sum_mul`. No ultrametric property is involved. `NontriviallyNormedField` already supplies the `Field` instance the statement needs, so deleting this instance leaves the statement elaborating and true.
- `[CompleteSpace K]` (theorem): Same argument: the identity is a finite-sum regrouping over a field, using only `Fz u 0 = 0` and the bounds hg and hh. Completeness of K is never needed. The statement still elaborates with only `NontriviallyNormedField K`, which gives the `Field` structure used by `Fz`. The two instances are independent and can both be deleted.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal.Ψ₂Sq_𝓦p_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L273-L277) — `flt-anthropic-0125`

Snippet: `samples/flt-anthropic/flt-anthropic-0125.lean`

- `(hp2 : p ≠ 2)` (theorem): The statement stays true for p = 2. Here Ψ₂Sq = C 4 * X^3 + C b₂ * X^2 + C (2*b₄) * X + C b₆ (Mathlib DivisionPolynomial/Basic), with b₂ = a₁^2 + 4*a₂. For 𝓦p p = ⟨X 0, X 1, X 2, X 3, X 4⟩ the X^2-coefficient is b₂ = X 0 ^ 2 + 4 * X 1 in MvPolynomial (Fin 5) (ZMod p). Evaluating at X 0 ↦ 1 and the other variables ↦ 0 gives 1, which is nonzero in ZMod p because p is prime (so p ≠ 1, supplied by [Fact p.Prime]). So the coefficient is nonzero for every prime p, including 2, where the X^3 coefficient 4 does vanish. The proof changes by taking `coeff _ 2` instead of `coeff _ 3`, simp-ing with the b₂ definition, and applying `MvPolynomial.eval` at ![1,0,0,0,0] to get 1 = 0 in ZMod p, a contradiction. The current proof uses hp2 only through four_ne_zero_Rp. [Fact p.Prime] is still needed, since for p = 1 the ring is trivial and Ψ₂Sq = 0.

### [`P2MW.S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.KcSemiLocalIwasawaHaar.mem_K_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_nhds_forall_ratio_mul_sqrtRatio_mul_twistedWeighted_eq_of_norm_sub_le_of_normString_diagUnits2_eq_of_areMatchingLocal.lean#L1008-L1009) — `flt-anthropic-0126`

Snippet: `samples/flt-anthropic/flt-anthropic-0126.lean`

- `[NumberField L]` (variable): The statement only uses `G`, `E`, `𝒦 = AutomorphicForm.semiLocalIntegralSet K L v` and `𝒪 = AutomorphicForm.semiLocalIntegers K L v`, with matrix entries and inverses. None of this needs `NumberField L`. In Definitions/Def_AutomorphicForm_TwistedOrbital.lean the same section variables are in force (Field K, NumberField K, Field L, NumberField L, Algebra K L). There, `zero_mem_semiLocalIntegers`, `one_mem_semiLocalIntegers` and `one_mem_semiLocalIntegralSet` are stated with `omit [NumberField L] in`, and they mention `semiLocalIntegers K L v` and `semiLocalIntegralSet K L v`. Those lemmas compile, so the two definitions do not take `[NumberField L]` as an argument. `semiLocalIntegers` is a `Set.range` of `tensorAdicCompletionIntegersTo`, and the lemmas about that map omit the Dedekind, integrality and fraction-ring hypotheses on `𝓞 L`. So the statement elaborates without `[NumberField L]`. It stays true, since it is just the definitional unfolding of `integralUnitsSet`. The proof `Iff.rfl` does not use the instance, so it still works if `[NumberField L]` is dropped with `omit [NumberField L] in`.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.AlgebraicCurve.HolRingFGAux.exists_fin_generators`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.lean#L590-L610) — `flt-anthropic-0132`

Snippet: `samples/flt-anthropic/flt-anthropic-0132.lean`

- `(hN : N.Nonempty)` (theorem): The statement is still true for N = ∅. Take n = 0 and z the empty family, so Algebra.adjoin k (Set.range z) is just the image of k in K. The first conjunct is vacuous. The second says that any f ∈ K lying in Q.toValuationSubring for every place Q is algebraic over k. Since k is algebraically closed, such an f then lies in k. A Place is a nontrivial discrete valuation subring of K containing k. Here K is a function field of one variable over the algebraically closed field k: it is essentially of finite type, and Ω[K/k] is free of rank 1, so the transcendence degree is 1. Suppose f is transcendental over k. Then K is finite over k(f). Take the integral closure of k[1/f] in K, which is a Dedekind domain. A prime over (1/f) gives a place Q with f ∉ Q.toValuationSubring. This uses the same ofHeightOneSpectrum and integral-closure machinery as holRing_fg, with 1/f in place of t. So the empty-N case is the classical fact that functions regular on the whole curve are constant. The proof therefore needs a short case split on N = ∅. In that case, use n = 0 and the argument above, or the degree-zero property of principal divisors together with finite residue fields. For nonempty N, proceed as before. hN is used only to feed holRing_fg and exists_fn, which pick a place Q₀ ∈ N, so it is a proof convenience and not needed for the truth of the statement.

### [`P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.MapsDvdSol.opFamily_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.lean#L343-L365) — `flt-anthropic-0134`

Snippet: `samples/flt-anthropic/flt-anthropic-0134.lean`

- `[IsDomain 𝒪]` (variable): 𝒪 is an argument because the statement mentions it, so this instance-implicit variable is pulled in. The statement only needs `CommRing 𝒪`, since `opFamily M H S 𝒪` needs `CommRing 𝒪` and `NeZero M` and nothing else. The proof uses `diamondL_top_eq_one`, whose signature takes only `(𝒪 : Type) [CommRing 𝒪]`. It also uses `CohCarrier.heckeT_comm_of_prime`, whose hypotheses are `NeZero ℓ`, `NeZero ℓ'`, primality, coprimality and `AddCommGroup V`; here V = 𝒪, which gets `AddCommGroup` from `CommRing`. The domain property is never used, so the theorem holds and the same proof works after deleting it, for example with `omit [IsDomain 𝒪] in`. It can be deleted independently of the other two.
- `[CharZero 𝒪]` (variable): The statement and the proof need only `CommRing 𝒪`, as for `[IsDomain 𝒪]`. `heckeT_comm_of_prime` and `diamondL_top_eq_one` need no characteristic assumption. The proof never uses this instance, so the same proof works without it. It can be deleted independently.
- `[IsLocalRing 𝒪]` (variable): The statement and the proof need only `CommRing 𝒪`, as for `[IsDomain 𝒪]`. The lemmas the proof relies on require no local-ring assumption. The proof never uses this instance, so the same proof works without it. It can be deleted independently.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.C2Count.natCard_finPts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.lean#L214-L257) — `flt-anthropic-0143`

Snippet: `samples/flt-anthropic/flt-anthropic-0143.lean`

- `(hm : 0 < m)` (theorem): hm follows from hmp together with the variable [Fact p.Prime], which is an argument of the theorem because p occurs in the statement. If m = 0, then Nat.Coprime 0 p says gcd 0 p = p = 1 (Nat.coprime_zero_left). That contradicts p being prime, since a prime is > 1. So 0 < m always holds under the remaining hypotheses, and the statement stays true after deleting hm. In the proof, hm is only used to build the witness ⟨m, hm, hpm, _⟩ for hinj and hsurj. Replace it by a local `have hm : 0 < m := Nat.pos_of_ne_zero (fun h => by subst h; have := Nat.coprime_zero_left p |>.mp hmp; exact (Fact.out : p.Prime).one_lt.ne' this)`. The rest of the proof is unchanged.

### [`P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve.SmoothedFundamentalProof.finite_support_smul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.lean#L435-L442) — `flt-anthropic-0144`

Snippet: `samples/flt-anthropic/flt-anthropic-0144.lean`

- `[Γ.FiniteIndex]` (variable): The statement doesn't need this instance. `ModularCurve.smoothedFundamental Γ T z` is defined in Definitions/Def_ModularCurve_SmoothedFundamental.lean as `∑ᶠ q : SL(2,ℤ) ⧸ Γ, puCut T (mob (Quotient.out q) z)`, a finsum that takes no finite-index hypothesis. So the statement elaborates and stays true without it. The only places the proof uses it are `mem_carrier_of_ne_zero`, `isCompact_carrierH` and the scoped `Fintype` instance built from it.

Without it, the proof can go as follows. `hasFiniteSupport_puCut_mob T τ` gives a finite set S of δ in SL(2,ℤ) with `puCut T (mob δ τ) ≠ 0`. It needs no finite-index assumption. Suppose γ ∈ Γ is in the support, so the finsum at `γ • τ` is nonzero. Then some term is nonzero, because otherwise the finsum would be 0 via `finsum_zero`. That gives a coset q with `puCut T (mob (out q) (γ • τ)) ≠ 0`. By `coe_smul` and `mob_mob` this is `puCut T (mob (out q * γ) τ) ≠ 0`, so `s := out q * γ ∈ S`. Since `out q ∈ q·Γ` (left cosets), `s ∈ q·Γ`, so `q = ⟦s⟧` and `γ = (out ⟦s⟧)⁻¹ * s`. Hence the support lies in the image of the finite set S under `s ↦ (out ⟦s⟧)⁻¹ * s`, which is finite. This works for any Γ, including infinite index. For infinite index the finsum may be a junk value, but the argument only uses that a nonzero finsum has a nonzero term.

So `[Γ.FiniteIndex]` can be deleted with a changed proof: the current proof's use of `mem_carrier_of_ne_zero` and `finite_moving` is replaced by the finite-set argument above.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.P2mFlatIsog.ringKrullDim_stalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.lean#L246-L300) — `flt-anthropic-0150`

Snippet: `samples/flt-anthropic/flt-anthropic-0150.lean`

- `[IsIntegral Y]` (theorem): Y is not required to be integral. Nothing in the statement needs this instance: fY only needs LocallyOfFiniteType, and the conclusion only mentions the stalk rings. The hypothesis is implied by the others up to nilpotents, and nilpotents do not change Krull dimension. Since h is surjective and X is irreducible, Y is irreducible, because it is the image of X. Since X is reduced, h factors through Y_red, and the factored map X → Y_red is still finite and surjective. Y_red is reduced and irreducible, so it is integral, and it is locally of finite type over K because Y is. The stalk of Y at a point is a quotient by its nilradical of the stalk of Y_red at the same point, and Krull dimension is unchanged because the prime spectrum is the same. Applying the existing argument to X → Y_red therefore gives ringKrullDim(O_{X,x}) = ringKrullDim(O_{Y_red,h x}) = ringKrullDim(O_{Y,h x}). The only places where the current proof uses integrality of Y are injectivity of h^# on affine opens (via basicOpen_eq_bot_iff, which needs reducedness) and the domain hypothesis in height_comap_eq. Both are obtained after passing to Y_red. The other hypotheses cannot be dropped. IsIntegral X is needed: X = Y ⊔ pt maps finitely and surjectively onto a positive-dimensional Y, and the stalk at the extra point has dimension 0. Surjective and IsFinite are also needed.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.R4ODGlue.eq_of_proj_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.lean#L415-L421) — `flt-anthropic-0167`

Snippet: `samples/flt-anthropic/flt-anthropic-0167.lean`

- `(hcomm : q'.comp p' = q''.comp p'')` (variable): The proof only uses hcomm to show that (p' b₁, p'' b₁) is a compatible pair. It can be dropped, because hpb alone gives injectivity of b ↦ (p' b, p'' b). The pair (0,0) is compatible, since q' 0 = 0 = q'' 0. So hpb gives a unique b with p' b = 0 ∧ p'' b = 0, and b = 0 is such an element. Hence p' b = 0 ∧ p'' b = 0 implies b = 0. Now suppose p' b₁ = p' b₂ and p'' b₁ = p'' b₂. Then b₁ - b₂ satisfies p' (b₁ - b₂) = 0 and p'' (b₁ - b₂) = 0, because ring homomorphisms preserve subtraction. So b₁ - b₂ = 0, i.e. b₁ = b₂. This is a short replacement proof that does not mention hcomm. hcomm does not occur in the conclusion or in any other binder. The theorem stays true and provable without it, so it can be omitted with `omit hcomm in`.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.AlgebraicCurve.AlgebraicCurve.adeleBddPrincipal_eq_comap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean#L791-L793) — `flt-anthropic-0183`

Snippet: `samples/flt-anthropic/flt-anthropic-0183.lean`

- `[HasPrincipalDivisors K F]` (theorem): The statement does not mention it: adeleBddPrincipal, adeleBdd, adeleSpace and globalSub are defined without any HasPrincipalDivisors argument. It is used only in the proof, to get globalSub ≤ adeleSpace (via diagonal_mem_adeleSpace). The equality holds without it, with S = adeleBdd D ≤ C = adeleSpace (adeleBdd_le_adeleSpace, no hypothesis) and T = globalSub arbitrary: S.comap C.subtype ⊔ T.comap C.subtype ≤ (S ⊔ T).comap C.subtype by monotonicity of comap. Conversely, if x ∈ C and x = s + t with s ∈ S, t ∈ T, then t = x - s ∈ C since S ≤ C, so s ∈ S∩C and t ∈ T∩C, and x lies in the sup of the two comaps. A Lean proof pushes forward along the injective C.subtype with map_sup and map_comap_subtype. That reduces it to S ⊔ (T ⊓ C) = (S ⊔ T) ⊓ C, which is the modular law and follows from S ≤ C. The existing helper Submodule.comap_subtype_sup_of_le_of_le assumes T ≤ C, so it would need a variant or direct proof that drops that assumption. I did not check the exact Mathlib name for the modular law.

### [`P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE.ell_sub_eq_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.lean#L175-L187) — `flt-anthropic-0184`

Snippet: `samples/flt-anthropic/flt-anthropic-0184.lean`

- `(hf0 : f ≠ 0)` (theorem): The hypothesis is only used to cancel f against f⁻¹ in the linear equivalence. If f = 0, then hP says P v = v.ord 0 = 0 for every place v, by `Place.ord_zero` (`v.ord 0 = 0`, a simp lemma in DivisorClassGroup.lean). `Divisor K F` is `Place K F →₀ ℤ`, so P = 0 by `Finsupp.ext`. Then `E - P = E` and `ell (E - P) = ell E` holds trivially. So the statement is true without hf0. A proof does `rcases eq_or_ne f 0 with rfl | hf0`. The first case uses `have : P = 0 := Finsupp.ext fun v => by simp [hP v]`, then `subst this; simp`. The second case is the existing proof.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.eq_span_tInvChart_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L2727-L2734) — `flt-anthropic-0199`

Snippet: `samples/flt-anthropic/flt-anthropic-0199.lean`

- `(ht : Transcendental κ t)` (variable): The proof only uses ht to get `transcendental_inv κ t ht`. The statement stays true when t is algebraic over κ, so ht can be dropped.

The argument is a case split on whether u := t⁻¹ is transcendental over κ. `chartRing κ S` is defined as the integral closure of `Algebra.adjoin κ S` in L. The hypothesis hchartInv says that `chartRing κ {u}` equals `{aeval u f | f : κ[X]}`.

1. If u is transcendental over κ, the existing proof applies. `eq_span_of_pow_mem κ t⁻¹ _ hchartInv (m := 1) 0 𝔮` only needs `Transcendental κ t⁻¹`, and this case supplies that directly.

2. If u is algebraic over κ, then by hchartInv the ring `chartRing κ {u}` is `κ[u]`, a subring of the field L, so it is a domain. Because u is algebraic over the field κ, `κ[u]` is a field. In a field a prime ideal 𝔮 is ⊥.
   - If u ≠ 0 (t is algebraic and nonzero), tInvChart is a unit of the field. Then tInvChart ∈ 𝔮 forces 𝔮 = ⊤, contradicting primality, so the case is vacuous.
   - If u = 0 (t = 0), then tInvChart = 0. By hchartInv the ring is the image of κ, which is a field. So 𝔮 = ⊥ = span {0} = span {tInvChart}. The omitted `[Fact (t ≠ 0)]` already shows this degenerate case is not excluded.

So the conclusion holds in both cases. hchartInv is still needed, since otherwise chartRing could be a larger integral closure.

### [`P2MW.S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.RoadA.coe_τ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem_level.lean#L325-L326) — `flt-anthropic-0219`

Snippet: `samples/flt-anthropic/flt-anthropic-0219.lean`

- `[NeZero M]` (variable): The statement never uses `NeZero M`. `modularFunctionFieldBar M` is `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull M)`. `modularFunctionFieldFull N` is `adjoin ℚ (divisorExpansions N)`, and neither definition's body uses `NeZero N`. `Def_ModularCurve_ArithmeticGalois.lean` defines `modularFunctionFieldBar` with only `variable (N : ℕ)` and no `NeZero`. `Def_ModularCurve_AtkinLehnerPartial.lean` writes `modularFunctionFieldFull (N * ℓ)` with `N` unconstrained, and this compiles. So neither takes the instance. `τ M σ` is an abbrev for `arithmeticRingAut (modularFunctionFieldFull M) σ`, which needs only `[Field L] [Algebra ℚ L]`, so it does not use the instance either. `coeffMap` and `LaurentSeries Lb` do not involve `M`. The `variable` line makes `[NeZero M]` an argument of the theorem only because its type mentions `M`. The proof is `rfl`, which unfolds `τ` and `arithmeticRingAut` and uses no instance. The theorem is therefore true and provable with the argument deleted, for example via `omit [NeZero M] in`, with no degenerate cases to check (`M = 0` just gives another field `modularFunctionFieldFull 0`).

### [`P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc.Bdd.mul_small`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PowerSeries_dvd_of_forall_taylorShift_order_le.lean#L132-L135) — `flt-anthropic-0231`

Snippet: `samples/flt-anthropic/flt-anthropic-0231.lean`

- `(hC : 0 ≤ C)` (theorem): It follows from hP : Bdd C P. Bdd C P unfolds to ∀ k, ‖coeff k P‖ ≤ C, so hP 0 gives 0 ≤ ‖coeff 0 P‖ ≤ C. Delete the binder and start the proof with `have hC : 0 ≤ C := (norm_nonneg _).trans (hP 0)`. The rest of the proof is unchanged. Small, Bdd and Small.mul are defined in this file.
- `(hC' : 0 ≤ C')` (theorem): It follows from hQ : Small ρ C' m Q. Small unfolds to ∀ k, ‖coeff k Q‖ ≤ C' * ρ^(m-k). At k = m this reads ‖coeff m Q‖ ≤ C' * ρ^0 = C', so C' ≥ 0 whatever ρ is. Delete the binder and start the proof with `have hC' : 0 ≤ C' := by simpa using (norm_nonneg _).trans (hQ m)`. The rest of the proof is unchanged. It can be deleted together with hC, since each is derived from a different hypothesis (hP and hQ).

### [`P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.EtaleCoordK1a.rankAtStalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean#L13-L24) — `flt-anthropic-0236`

Snippet: `samples/flt-anthropic/flt-anthropic-0236.lean`

- `[Module.Flat S M]` (theorem): `Module.rankAtStalk M p` is defined as `finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)`. The proof only uses flatness (and finite presentation) to get local constancy of the rank, which lets it reduce to p = ⊥. That reduction is not needed. Since S is a domain, every x ∈ p.asIdeal.primeCompl is nonzero, because 0 ∈ p. So `p.asIdeal.primeCompl ≤ nonZeroDivisors S` holds for every prime p. The `hle` argument in the proof then works for any p. `IsLocalization.rank_eq` and `IsLocalizedModule.rank_eq` (Mathlib/LinearAlgebra/Dimension/Localization.lean) need only `hp : p ≤ R⁰`. They give `rank (S_p) (M_p) = rank S M = n`, and `finrank_eq_of_rank_eq` finishes. The theorem is therefore true and provable without Flat.
- `[Module.FinitePresentation S M]` (theorem): The same direct argument works for every prime p. `primeCompl p ≤ nonZeroDivisors S` holds in a domain. `IsLocalization.rank_eq` and `IsLocalizedModule.rank_eq` need no finite presentation, only `hp : p ≤ R⁰`. So `rank (S_p) (M_p) = rank S M = n`, and `finrank_eq_of_rank_eq` gives the result. Finite presentation was used in the original proof only for `isLocallyConstant_rankAtStalk`, which is no longer needed. Both this and Flat can be deleted, individually or together.

### [`P2MW.S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.SupersingularTop3.mem_of_ord_nonneg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.lean#L40-L46) — `flt-anthropic-0240`

Snippet: `samples/flt-anthropic/flt-anthropic-0240.lean`

- `(hf : f ≠ 0)` (theorem): The conclusion is `f ∈ w.toValuationSubring`. For f = 0 this is `zero_mem`, whatever `w.ord 0` is, so the case excluded by `hf` is true anyway. A proof without `hf` starts with `by_cases hf : f = 0`. In that case, `subst hf; exact w.toValuationSubring.zero_mem`. In the other case, the existing proof runs unchanged. `hf` is used only to apply `exists_unit_mul_zpow`. The other arguments `K`, `F`, their field instances, `Algebra K F`, `w` and `h` are needed to state the theorem. `Place K F` needs the algebra instance, and `h` is not removed.

### [`P2MW.S_RubinSilverberg_exists_polynomial_rsFamily.M4cP2.D52.PhiA_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_RubinSilverberg_exists_polynomial_rsFamily.lean#L410-L414) — `flt-anthropic-0247`

Snippet: `samples/flt-anthropic/flt-anthropic-0247.lean`

- `(hj : j < 21)` (theorem): The statement stays true for every j, but the proof needs a new interpolation step in t that I did not write out. For fixed s, write the difference sidePlusA − sideMinusA in the variable t. The left part comes from lhsPairAG, which is a combination of P5^a·R^b with 5a+5b ≤ 20, where P5 and R have degree 5 in t. Their t-degree is therefore at most 20. The right part is hornerG over the 21-row table tabA (lines 27–47), so its degree in t is at most 20. The coefficients involve only s, so they are constants in t. So for each s, the difference is a polynomial in t of degree ≤ 20 over ℤ. gridA, via checkA_0, shows it vanishes at t = 0,…,20, which is 21 distinct points. It is therefore the zero polynomial in t, and it vanishes at every natural t = j, including j ≥ 21. To prove it, form the ℤ[T]-polynomial with constant coefficients hornerC … s and variable T. Bound its natDegree by 20, which compute_degree should do as in natDegree_PhiA_le. Then apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero with the points 0..20. This gives eval_PhiA for all j. The rest of the existing proof of PhiA_eq (the degree bound natDegree_PhiA_le and the 197 roots s) then works unchanged for every j. The binder hj is used only to feed eval_PhiA/gridA, and the junk-value cases don't matter here.

### [`P2MW.S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.lean#L16-L30) — `flt-anthropic-0249`

Snippet: `samples/flt-anthropic/flt-anthropic-0249.lean`

- `[W.IsElliptic]` (theorem): The proof never uses `W.IsElliptic`. The conclusion `W.IsTwoKernel (X - C (Q.coordsOrZero).1)` is a structure over a general `CommRing`, so it needs no ellipticity. `W.toAffine.Point` and its `AddCommGroup` instance (Mathlib `Affine/Point.lean`, line 805, in the section with only `[Field F] [DecidableEq F]`) do not need it either. `addOrderOf Q` therefore elaborates without it. The only external lemma in the proof, `WeierstrassCurve.eval_Psi2Sq_of_two_nsmul_eq_zero`, has signature `{F} [Field F] [DecidableEq F] {W : Affine F} {x y} (h : W.Nonsingular x y) (h2 : 2 • some x y h = 0)`, with no `IsElliptic`. The nonsingularity hypothesis comes from the point `Q = some x y hxy` itself. The remaining steps (`natDegree_X_sub_C`, `coeff` computations, `addOrderOf_zero`, `addOrderOf_nsmul_eq_zero`) are purely algebraic. So deleting the binder leaves the theorem true, and the same proof compiles.

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.QMHecke12.exists_generator`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.lean#L368-L422) — `flt-anthropic-0252`

Snippet: `samples/flt-anthropic/flt-anthropic-0252.lean`

- `(hι : Function.Injective ι)` (variable): The proof of exists_generator never uses hι. The only place the injectivity of ι could matter is the injectivity of qmPeriodMap ι τ. The proof gets that from `QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hO ha hb ι τ`. That lemma takes only `IsOrder Λ`, `a ≠ 0`, `b ≠ 0`, ι and τ, and has no injectivity hypothesis on ι. The other steps are `qmPeriodMap_mul` (pure matrix algebra), the lemma `exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt` and `exists_isUnitOf_nrd_eq_neg_one`. None of these mention ι or hι. So the theorem stays true and provable with the same proof once hι is removed, for example with `omit hι in` and without `hι` in the `include` line. ι stays in the statement through qmPeriodLattice and qmPeriodMap. Its injectivity also holds automatically here, because ℍ[ℚ,a,b] is a division algebra when a, b ≠ 0, but the proof doesn't need that.

### [`P2MW.S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.AlgebraicCurve.AlgebraicCurve.Place.stichtenothGenusExists_of_isFractionRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean#L2159-L2166) — `flt-anthropic-0261`

Snippet: `samples/flt-anthropic/flt-anthropic-0261.lean`

- `[HasPrincipalDivisors K F]` (variable): The theorem also takes `[IsCurveOver K F]`, and `class IsCurveOver : Prop extends HasPrincipalDivisors K F` (Definitions/Def_AlgebraicCurve_IsCurveOver.lean). Its parent projection `IsCurveOver.toHasPrincipalDivisors` is therefore an instance, so the variable is implied by the theorem's own binder. The statement does not need the variable to elaborate. `StichtenothGenusExists`, `LSpace`, `TranscendenceTower` and `RegularOutside` take no `HasPrincipalDivisors` argument. `HasPrincipalDivisors` is a Prop, so there is no diamond. Add `omit [HasPrincipalDivisors K F] in` before the theorem. The proof term is unchanged, because `hasPoleDivisorPackage_of_isFractionRing` and `stichtenothGenusExists_of_hasPoleDivisorPackage` then find `HasPrincipalDivisors K F` from `IsCurveOver K F`. The statement is unchanged.
- `[Nonempty (Place K F)]` (theorem): This is derivable from the package that the proof builds. `hasPoleDivisorPackage_of_isFractionRing T hA` gives `HasPoleDivisorPackage K F`, so `h.some` is a `PoleDivisorPackage` P. It has `hn_pos : 0 < n` and `degB_eq : Divisor.degree B = n`. If `Place K F` were empty, `Divisor K F = Place K F →₀ ℤ` would be a subsingleton, so `B = 0` and `degree B = 0` (the degree is an `AddMonoidHom`). That contradicts `n > 0`. Hence `Nonempty (Place K F)` holds. The proof becomes `obtain ⟨P⟩ := ...; haveI : Nonempty (Place K F) := (by_contra/isEmpty argument above); exact stichtenothGenusExists_of_poleDivisorPackage P`. Instances are Props, so `haveI` is fine, and the conclusion `StichtenothGenusExists K F` is unchanged. Its `Nonempty` component is exactly the derived fact. This is independent of the first entry. I did not claim that `[FiniteDimensional K (LSpace 0)]` is removable.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.WeierstrassCurve.WeierstrassCurve.ModularCurve.kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean#L3405-L3408) — `flt-anthropic-0263`

Snippet: `samples/flt-anthropic/flt-anthropic-0263.lean`

- `[IsScalarTower R₀ F F']` (variable): The statement `Transcendental F (polyToFunctionField (W⁄F') X)` only needs `Algebra R₀ F'` (for `W⁄F'`) and `Algebra F F'`. That gives `Algebra F (W⁄F').toAffine.FunctionField` through `AdjoinRoot` and `FractionRing`. The proof is `Transcendental.of_tower_top F (L := F') (transcendental_polyToFunctionField_X (W := W⁄F'))`. It needs only `IsScalarTower F F' (FunctionField)`, which Mathlib's generic AdjoinRoot/FractionRing scalar-tower instances supply from `Algebra F F'`. R₀ does not enter. The helper `transcendental_polyToFunctionField_X` uses only `[Field F']` and `polyToFunctionField_injective`. So the theorem stays true and provable without it, e.g. via `omit [IsScalarTower R₀ F F'] in`.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]` (variable): The statement is about `W⁄F'` and never mentions `W⁄F`. The proof uses only `transcendental_polyToFunctionField_X` and `Transcendental.of_tower_top`. Neither refers to any place gate or centring property, and nothing else in the statement depends on this instance. Deleting it with `omit` leaves the statement and proof unchanged.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]` (variable): The statement only involves `W⁄F'`, and the proof is a transcendence-tower argument that does not use `AbelTheorem`. Nothing else in the statement depends on this instance, so it can be omitted.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]` (variable): Transcendence of `X` over `F` follows from `polyToFunctionField_injective` and `Transcendental.of_tower_top`. Neither uses the centring property of the place gate on `W⁄F'`. No other binder or the conclusion depends on this instance, so it can be omitted.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]` (variable): Neither the statement nor the proof uses Abel's theorem. The helper `transcendental_polyToFunctionField_X` is proved from `polyToFunctionField_injective` alone, and no other binder depends on this instance, so it can be omitted.

### [`P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.lean#L229-L413) — `flt-anthropic-0266`

Snippet: `samples/flt-anthropic/flt-anthropic-0266.lean`

- `(hsurj : Function.Surjective π.base)` (theorem): hsurj follows from the other hypotheses, so it can be deleted. Its only use is in `range_ι_comp_eq_univ`, to show `π.base '' W ∪ π.base '' Wᶜ = univ`. Derive `Set.range π.base = univ` as follows. Since `π` is finite, `π.isClosedMap` makes `range π.base` closed. If it were not all of `X`, its complement would be a nonempty open `V : X.Opens`. Then `π ⁻¹ᵁ V = ⊥`, because no point of `C` maps into `V`. So `Γ(C, π ⁻¹ᵁ V)` is a subsingleton: use `CommRingCat.subsingleton_of_isTerminal (C.sheaf.isTerminalOfEqEmpty ...)`, the same trick the proof already uses, or the instance `Subsingleton Γ(X, ⊥)`. By `hsec V`, `π.app V : Γ(X,V) → Γ(C, π⁻¹ᵁ V)` is injective, so `Γ(X,V)` is a subsingleton. But `Scheme.component_nontrivial` (Mathlib/AlgebraicGeometry/Properties.lean) gives `Nontrivial Γ(X,V)` whenever `Nonempty V`. This is a contradiction, so `V` is empty and `π` is surjective. The statement is unchanged and stays true, and the proof only gains this short derivation at the point where `hsurj` is used.

### [`P2MW.S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.lean#L203-L596) — `flt-anthropic-0267`

Snippet: `samples/flt-anthropic/flt-anthropic-0267.lean`

- `(htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)` (theorem): `htame` is a plain Prop hypothesis. It appears only in its own binder, at line 211 of the file. Nothing else in the statement mentions it, and the proof never refers to it. The final unipotency goal comes from `HeckeRing.isUnipotentOnInertiaAt_of_dvd_of_not_isUnramifiedAt`, which is applied without `htame`. The other goals are closed from `hmin`, `hN`, `hNmin` and the rest, again without `htame`. Deleting the binder therefore leaves the proof compiling unchanged, and the theorem stays true and provable.

### [`P2MW.S_Function_orbitCensus_of_dihedralThree_relations.P2MKcOrbitCensus.b_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean#L14-L17) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- `[Fintype X]` (variable): The statement `Function.Injective b` only needs X and b. [Fintype X] is taken as an argument only because it is instance-implicit and X is already an argument. The proof (b (b (b x)) = x gives b (b (b x)) = b (b (b y)) from b x = b y, so x = y) never uses finiteness, and the result holds for any type. It can be omitted with `omit [Fintype X] in`.
- `[DecidableEq X]` (variable): The statement and proof do not use decidable equality. The theorem is just injectivity of b, which follows from hb alone, so the instance is only auto-included as an instance-implicit variable over X. It can be omitted with `omit [DecidableEq X] in`. This is independent of [Fintype X].

### [`P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.KcHaarQuotientMulRight.lintegral_density_mul_comp_mul_right_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.lean#L75-L109) — `flt-anthropic-0270`

Snippet: `samples/flt-anthropic/flt-anthropic-0270.lean`

- `[SFinite μH]` (theorem): The statement mentions μH only through `HaarQuotient.density H μH`, a plain definition that needs no SFinite instance. In the proof, `SFinite μH` is used only by the helper `measurable_density` (for `lintegral_prod_right'`). `lintegral_density_mul_eq_one`, `lintegral_withDensity_eq_of_admissible` and `map_mk_withDensity_eq_smul_measure` do not take it. It is redundant given the other hypotheses. `hH : IsClosed (H : Set G)` gives `SigmaCompactSpace H` via `IsClosed.sigmaCompactSpace` (Mathlib/Topology/Compactness/SigmaCompact.lean:267), because G is locally compact and second countable and so σ-compact. Then `[μH.IsHaarMeasure]` gives `SigmaFinite μH` through the instance `MeasureTheory.Measure.IsHaarMeasure.sigmaFinite [SigmaCompactSpace G]` (Mathlib/MeasureTheory/Group/Measure.lean:921), and `SFinite μH` follows from that. So the theorem stays true and provable after deleting it. The change to the proof is to add `haveI : SigmaCompactSpace H := hH.sigmaCompactSpace` before calling `measurable_density`. I did not check whether `[SFinite μ]` can also be dropped: the helper lemmas it feeds into depend on it, and I could not justify deleting it.

### [`P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.UqNSol.fstDiv_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean#L358-L366) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- `[hqN : Fact (¬ q ∣ N)]` (variable): hqN is an instance-implicit variable whose type mentions only q and N, which are already arguments, so the theorem takes it automatically. The statement never uses it. `PlaceSpecialization.fstDiv` is defined in Definitions/Def_ModularCurve_GlueData.lean as `D.filter P.IsStrictFst`. That file has no `Fact (¬ q ∣ N)` variable, and neither does `PlaceSpecialization` (which needs only `Fact q.Prime`, `NeZero N` and `CharP k q`). `Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N*q))` also elaborates in that file without it. So the statement `P.fstDiv (∑ i ∈ s, f i) = ∑ i ∈ s, P.fstDiv (f i)` is the same without hqN, and it is true: `fstDiv` is `Finsupp.filter`, which is additive. The only way the proof touches hqN is the call to the local `fstDiv_add`, which itself takes hqN from the same `variable` line. Replace that call with `Finsupp.filter_add` (the lemma `fstDiv_add` uses). The `empty` case already uses `Finsupp.filter_zero` and needs no hqN. Use `omit hqN in` before the theorem.

### [`P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.LCMazur.OrdQ.span_singleton_eq_range_ordProj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.lean#L263-L272) — `flt-anthropic-0275`

Snippet: `samples/flt-anthropic/flt-anthropic-0275.lean`

- `[IsLocalRing A]` (variable): The statement does not need [IsLocalRing A] to elaborate. `charpoly` and `finrank` need only Module.Free and Module.Finite, and `ordProj` needs only CommRing. The local hypothesis is used only through `exists_basis_range_ordProj`, which in turn uses `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`. The theorem is still true for any commutative ring A. Let ψ = φ - β and e = ordProj φ α β. Since α-β is a unit, ψ² = (α-β)ψ, so e is idempotent, and ψ has charpoly (X-(α-β))X. At each maximal ideal m, the localization A_m is a nontrivial local ring, and all hypotheses base-change to it. There, the charpoly forces rank e = 1: (X-1)^r X^{2-r} = (X-1)X forces r = 1 because -X ≠ 0 when A_m is nontrivial. So range e localizes to a free rank-1 summand. The existing local argument (`exists_basis_range_ordProj` plus `span_basis_eq_of_le`) gives (A·w)_m = (range e)_m. The inclusion range e ≤ A·w holds globally by the `hle` step, which is unchanged. The quotient (A·w)/range e therefore vanishes at every maximal ideal and so is zero, giving equality. The degenerate case, the trivial ring A, is trivial. The proof needs the extra localization step, but the claim holds without the hypothesis.

### [`P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.lean#L27-L40) — `flt-anthropic-0278`

Snippet: `samples/flt-anthropic/flt-anthropic-0278.lean`

- `(ha : a ≠ 0)` (theorem): The case a = 0 is also true, so ha can be removed. The proof splits on a = 0.

If a = 0: μ 0 = 0 < 1, since an absolute value sends 0 to 0 (`map_zero`). On the right, ⟨0, haA⟩ is the zero of A, which lies in `maximalIdeal A` (`Ideal.zero_mem`). A is a local ring, as the statement already uses `IsLocalRing.maximalIdeal A`. Both sides hold, so the iff holds.

If a ≠ 0: the existing proof applies unchanged, with `ha` supplied by the case split.

So `ha` is only needed in one branch and can be derived by `by_cases`, which makes it unnecessary as a hypothesis. The other hypotheses are all needed: `haA` is used in the conclusion's `⟨a, haA⟩`, and `hμA` links A and μ.

### [`P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.TH1Wanted2.inv_mem_and_const_mem_of_gaussPresentation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.lean#L874-L964) — `flt-anthropic-0285`

Snippet: `samples/flt-anthropic/flt-anthropic-0285.lean`

- `(hq3 : q = 3)` (theorem): The statement never mentions hq3 except as a hypothesis, and q only appears through fieldBar q M', qExpand and the general Fact q.Prime. The proof never refers to hq3. Its steps are coefficient and Laurent-series manipulations, plus qExpand_injective with N := q, which comes from Fact q.Prime. So the result holds for any prime q, and the argument can be deleted with the proof unchanged.
- `(hqM' : ¬ q ∣ M')` (theorem): hqM' is not used in the proof and not needed to elaborate the statement. fieldBar q M' and modularFunctionFieldBar M' are functions of q and M' alone, with NeZero M' coming from its own instance. The proof is a computation with q-expansions of jq and the valuation subring description hO. It uses no coprimality of q and M', so the theorem is still true and the same proof works without it.
- `(hK₁ : FiniteDimensional ↥k₀ ↥K₁)` (theorem): The finite-dimensionality of K₁ over k₀ is not needed to state the conclusion, because the algebra and subfield structure is given by the other hypotheses. The proof does not use it. It only uses hA₁, halg, hO, hj₁ and hj', and none of the instance or lemma steps need FiniteDimensional K₁. Deleting it leaves the proof unchanged.

### [`P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.lean#L110-L138) — `flt-anthropic-0294`

Snippet: `samples/flt-anthropic/flt-anthropic-0294.lean`

- `[IsDomain A]` (theorem): It is implied by the other hypotheses. K is a Field with Algebra A K and IsFractionRing A K. IsFractionRing.injective (Mathlib/RingTheory/Localization/FractionRing.lean, for any CommRing) makes algebraMap A K injective, and the file has an instance FaithfulSMul A K from IsFractionRing. IsDomain.of_faithfulSMul (Mathlib/Algebra/Algebra/Basic.lean) with IsDomain K from Field then gives IsDomain A. The statement never needs IsDomain A to elaborate: IsIntegrallyClosed A is an abbrev for IsIntegrallyClosedIn A (FractionRing A) and needs only CommRing, and ResidueField, Module.Finite, Module.Flat, IsFractionRing and IsAlgClosed need no IsDomain A either. The proof changes only by adding `haveI : IsDomain A := IsDomain.of_faithfulSMul A K` at the start. The GenLift helper lemmas take [IsDomain A] as a binder, and this local instance supplies it. The rest of the proof is unchanged, so the theorem remains true and provable without the binder.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.AlgebraicCurve.DiscRigidity.sum_filter_eq_of_degreeOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.lean#L80-L105) — `flt-anthropic-0299`

Snippet: `samples/flt-anthropic/flt-anthropic-0299.lean`

- `(hf : f ≠ 0)` (theorem): If f = 0 then hDf gives Df v = v.ord 0 = 0 for all v (Place.ord_zero: `v.ord (0:F) = 0`, since ord is defined as -(WithZero.log (adicValuation f)) with junk value 0). Hence Df = 0 (Divisor = Place L F →₀ ℤ), Df.support = ∅, and both filtered sums are empty sums equal to 0, so the conclusion holds. Proof: `by_cases hf : f = 0`; in the zero case show Df = 0 via Finsupp.ext/hDf/ord_zero and simp; in the nonzero case use the existing proof unchanged (hf is only used there for R.exists_smul_mem and ord_algebraMap_mul). Other hypotheses are unaffected.


## Formal Frontier (12 flagged)

### [`GradedRing.Veronese.adjoin_component_one_eq_top`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseDegreeOne.lean#L80-L104) — `formal-frontier-0005`

Snippet: `samples/formal-frontier/formal-frontier-0005.lean`

- `(hn : 0 < n)` (theorem): The statement elaborates without hn: `VeroneseRing 𝒮 n`, `component 𝒮 n j` and the `GradedRing (component 𝒮 n)` / algebra instances are defined for all n. They don't depend on positivity, and `selectedGradedMonoid` and `instGradedRing` are stated for every `n : ℕ`. The statement is also true for n = 0. There `VeroneseRing 𝒮 0 = ⨁_{j:ℕ} 𝒮 (0*j)`, which is a copy of 𝒮 0 in each degree j, with multiplication `of j a * of k b = of (j+k) (a*b)`. This is the polynomial-type ring 𝒮 0[X]. `component 𝒮 0 0` is the image of `of 0`, i.e. the constants, and `component 𝒮 0 1` contains `of 1 1`, which is X, since 1 ∈ 𝒮 (0*1) = 𝒮 0. Every generator `of j s` equals `of 0 s * (of 1 1)^j`, which lies in the adjoin. The additive induction `DirectSum.induction_on` then gives ⊤. So for n = 0 the conclusion holds even without hgen. The hypothesis hn is used in the proof only through `eval_mem_adjoin`, which uses `zeroRingEquiv` (needs injectivity), and through `inclusion_injective`. These are the only places hn enters. Deleting it means splitting on n: the n > 0 case keeps the existing proof, and the n = 0 case uses the short direct argument above. The hypothesis hgen is genuinely needed (for n = 1 the statement is equivalent to it), so only hn is removable.

### [`Nat.DivisionGrowth.affine_lower_bound`](https://github.com/FormalFrontier/sequence-growth/blob/7b7db3df8a043a09d037de4ff1eced6873404fb2/SequenceGrowth/Data/Nat/DivisionGrowth.lean#L68-L94) — `formal-frontier-0117`

Snippet: `samples/formal-frontier/formal-frontier-0117.lean`

- `(hs : 0 < s)` (theorem): The statement still holds with s = 0 (keeping hsn : s < n). In ℚ, (n:ℚ)/0 = 0. Also ((0-1:ℕ):ℚ) = 0, so the offset is n*0/(n-0) = 0. The conclusion becomes 0^m * u 0 ≤ u m. For m = 0 this is u 0 ≤ u 0. For m > 0 it is 0 ≤ u m, which holds because u m is a natural number. So the case s = 0 can be handled directly by cases on m, and hstep isn't needed there. For s > 0 the existing proof applies unchanged: rcases Nat.eq_zero_or_pos s, and use the original argument with hs obtained from the positive case. I did not read affine_step, which is where the original proof uses hs. The argument above doesn't depend on it. hsn is genuinely needed: for s = n the claim u 0 ≤ u m fails, for example with n = 2, u 0 = 1, u 1 = 0.

### [`IsKrasner.adjoin_rootSet_le_adjoin_rootSet_of_norm_coeff_sub_lt`](https://github.com/FormalFrontier/polynomial-root-stability/blob/ceae7822f6151ec6626678db1653054d3398cff3/PolynomialRootStability/Krasner.lean#L363-L391) — `formal-frontier-0152`

Snippet: `samples/formal-frontier/formal-frontier-0152.lean`

- `(hε : 0 < ε)` (theorem): hε is implied by hcoeff. Taking i = 0 gives ‖g.coeff 0 - f.coeff 0‖ < ε. Since 0 ≤ ‖·‖ (norm_nonneg), we get 0 < ε. So the statement is unchanged and still true without hε. In the proof, the only use of hε is as the argument to Mathlib's exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (Mathlib/Analysis/Normed/Field/Approximation.lean:115), which takes hε : 0 < ε. Replace it with `lt_of_le_of_lt (norm_nonneg _) (hcoeff 0)`. Every other argument of that lemma is still supplied by the remaining hypotheses. ε is still mentioned in hcoeff and hbound, so the statement still elaborates.

### [`Subgroup.exists_continuous_coset_representative`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ContinuousCosetRepresentative.lean#L55-L74) — `formal-frontier-0160`

Snippet: `samples/formal-frontier/formal-frontier-0160.lean`

- `[T2Space G]` (variable): T2Space G follows from the other variables, so it can be dropped with `omit [T2Space G] in`. The chain is: `TotallyDisconnectedSpace.t1Space` (Mathlib/Topology/Separation/Connected.lean) gives T1Space G from [TotallyDisconnectedSpace G]. T1 gives T0 by the standard instance. `IsTopologicalGroup.regularSpace` (Mathlib/Topology/Algebra/Group/Pointwise.lean) gives RegularSpace G from [Group G] [IsTopologicalGroup G]. `instT3Space` (T0 + Regular → T3Space) then `T3Space.t25Space` and `T25Space.t2Space` (Mathlib/Topology/Separation/Regular.lean) give T2Space G. So Lean can synthesize T2Space G from the remaining instances. The statement mentions only `C(G ⧸ H, G)`, which needs only the topology on G and the quotient topology. The proof, including the call to the helper lemma that may require [T2Space G], works unchanged, because instance resolution finds T2Space G. This is not the other hypotheses being used in a different way, only a redundant instance. Dropping it leaves the theorem true and provable.

### [`MvPowerSeries.isUnit_adicallyRestricted_iff_coeff_radical`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/UnitDetection.lean#L83-L92) — `formal-frontier-0162`

Snippet: `samples/formal-frontier/formal-frontier-0162.lean`

- `[IsAdicComplete I R]` (variable): The statement only mentions I, R, σ, f. Adic completeness is not needed for the statement to be true. I read `adicallyRestrictedSubring` and `IsAdicallyRestricted` in IdealAdicRestricted.lean: f is restricted iff for each k only finitely many coefficients lie outside I^k. This definition makes no use of completeness.

(→) Suppose f is a unit of the restricted subring. Its image in MvPowerSeries is a unit, so coeff 0 f is a unit of R. Reducing mod I (the k=1 case of the definition) gives a unit of (R/I)[σ] (MvPolynomial). By `MvPolynomial.isUnit_iff`, its constant coefficient is a unit and all other coefficients are nilpotent in R/I, i.e. lie in I.radical. This uses no completeness.

(←) Suppose coeff 0 f = u is a unit of R and every nonconstant coefficient is in I.radical. Write f = u(1+h), where h = u⁻¹(f − C u) is restricted, has constant term 0, and has all coefficients in the radical. Fix k.
- Only finitely many coefficients of h lie outside I^k. They generate a finitely generated ideal J ⊆ I.radical, so J^N ⊆ I for some N.
- All coefficients of h lie in L = J + I^k, and L^{Nk} ⊆ I^k. Hence h^{Nk} has all its coefficients in I^k.
- In MvPowerSeries, (1+h)⁻¹ = Σ_{n<Nk}(−h)^n + (−h)^{Nk}(1+h)⁻¹. The finite sum is restricted, and the last term has all coefficients in I^k.
- So only finitely many coefficients of the inverse lie outside I^k. Since k was arbitrary, the inverse is restricted, and f is a unit of the subring.

So the iff holds without `[IsAdicComplete I R]`. The current proof uses it through `isUnit_iff_quotient_of_isAdicComplete` and the reduction lemmas. It would need to be replaced by the direct argument above, which is more work but valid.

### [`FundamentalGroup.existsUnique_hom_of_isOpenCover`](https://github.com/FormalFrontier/fundamental-groupoids/blob/2fdb99858e3feb7a6a06ae10915f286364de2cc1/FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean#L404-L527) — `formal-frontier-0164`

Snippet: `samples/formal-frontier/formal-frontier-0164.lean`

- `(hU : IsPathConnected (U : Set X))` (theorem): The statement never mentions hU. Only the proof uses it, to build the connecting arrows `leftArrow` and `globalArrow`. Seifert–van Kampen for the base point p only needs U ∩ V to be path-connected and to contain p, together with U ∪ V = X and open U, V. This is a mathematical argument that I did not check in Lean.

1. Every loop at p is a product of paths. Each factor lies in U or in V, and its endpoints lie in U ∩ V. Since U ∩ V is path-connected, each endpoint can be joined to p inside U ∩ V.
2. Now take a homotopy of loops at p, subdivided into a grid. Let v be a grid vertex lying in U \ V. It is joined to p by a path in X, namely the image of a path in the homotopy square. Let a be the first time that path leaves U. Just before a the path lies in U ∩ V, because the path is in V there and U is open. So v is joined in U to a point of U ∩ V, hence to p.
3. So every grid vertex is path-connected to p inside the relevant set. A U-component of p that is not open causes no trouble.

The degenerate case behaves correctly: if U has path components that miss p, they are irrelevant to π₁(X,p).

The proof would have to be changed. The `leftArrow` data would only be defined on the path component of p in U, and the proof would restrict to the part of the cover that is reachable from p. The same argument works for hV, but I did not check that both can be dropped together.
- `(hV : IsPathConnected (V : Set X))` (theorem): The statement never mentions hV. Only the proof uses it, to build `rightArrow` and `globalArrow`. The argument is symmetric to the one for hU: only U ∩ V path-connected with p ∈ U ∩ V, open U and V, and U ∪ V = X are needed.

Loops at p decompose into pieces in U or V with endpoints in U ∩ V. Grid vertices of a homotopy that lie in V \ U are joined within V to U ∩ V, because V is open and the path first leaves V through U ∩ V. They are then joined to p inside U ∩ V. Components of V that miss p do not affect π₁(X,p). This is a mathematical argument that I did not check in Lean, and the proof would need reworking.

I believe hV can be deleted on its own. I did not check that hU and hV can both be deleted at once.

### [`GradedRing.Veronese.finiteType_of_finiteType`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseFiniteType.lean#L105-L126) — `formal-frontier-0179`

Snippet: `samples/formal-frontier/formal-frontier-0179.lean`

- `(hn : 0 < n)` (theorem): The statement is still true for n = 0, so hn can be dropped. I checked this by reading the definitions in GradedRings/Veronese.lean. I did not write or compile the new proof.

The definitions `VeroneseRing 𝒮 n`, `component 𝒮 n 0` and the `GradedRing (component 𝒮 n)` instance are all defined for every n, with no positivity assumption. Positivity is only used to prove injectivity of the inclusion, which gives `zeroRingEquiv`.

For n = 0, `VeroneseRing 𝒮 0 = ⨁ j, 𝒮 (0*j)`. Every summand is `𝒮 0` up to the propositional equality `0*j = 0`, so this is a polynomial-ring-like ring over `𝒮 0`. Multiplication is `of i a * of j b = of (i+j) (a*b)`. The ring `component 𝒮 0 0` is the image of `of 0`. Let t = `of 1 ⟨1,_⟩`. Then t^j = `of j 1`, and `of j a = of 0 a' * t^j`, where a' is a viewed as an element of `𝒮 (0*0)`. So `{t}` generates `VeroneseRing 𝒮 0` over `component 𝒮 0 0`, and the algebra is finite type (it is `(𝒮 0)[X]` over `𝒮 0`). Note that `1 ∈ 𝒮 (0*1)` holds because `𝒮 0` contains 1.

So the n = 0 case holds, and it does not even need the finite-type instance on `𝒮 0`. The proof can split on `n = 0` versus `0 < n`. The positive case is the current proof. The zero case uses `Subalgebra.fg_def` with the single generator t, proving `Algebra.adjoin _ {t} = ⊤` by `DirectSum.induction_on`. No degenerate case such as a trivial ring breaks this, because the argument is purely algebraic.

### [`AlgebraicGeometry.Proj.degreeScaledChartMap_preimage_basicOpen`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/DegreeScaledMap.lean#L453-L469) — `formal-frontier-0188`

Snippet: `samples/formal-frontier/formal-frontier-0188.lean`

- `(hn : 0 < n)` (theorem): The statement stays true for n = 0, and the n = 0 case reduces to the positive-degree case already available.

Write a := (i.2 : A). It has degree m := i.1 > 0 (`i.2.2 : a ∈ 𝒜 i.1`), and r ∈ 𝒜 n.

1. `hn` is only used to call `degreeScaledChartSpec_preimage_basicOpen` and, inside it, Mathlib's `Proj.awayι_preimage_basicOpen`. That lemma needs positive degree only because it uses `awayι` for g (the degree-n element) and the localization `Away.isLocalization_mul`, which is a proof artifact. The conclusion itself, `awayι ⁻¹ᵁ basicOpen r`, is meaningful for any r.

2. Case n > 0: use the existing proof unchanged.

3. Case n = 0: apply the n > 0 case to r' := r * a. Then r' ∈ 𝒜 (n + m) by `SetLike.mul_mem_graded`, and n + m = m > 0. By `map_mul`, f r' = f r * f a.
   - By `basicOpen_mul` (used in the file at line 201), basicOpen 𝒜 (r*a) = basicOpen 𝒜 r ⊓ basicOpen 𝒜 a, and basicOpen ℬ (f r * f a) = basicOpen ℬ (f r) ⊓ basicOpen ℬ (f a).
   - The chart map degreeScaledChartMap equals (basicOpenIsoSpec ℬ (f a)).hom ≫ Spec.map(mapDegreeMul) ≫ awayι 𝒜 a. Since `opensRange_awayι` gives (awayι 𝒜 a).opensRange = basicOpen 𝒜 a, its preimage of basicOpen 𝒜 a is ⊤.
   - The preimage of basicOpen ℬ (f a) under (basicOpen ℬ (f a)).ι is ⊤, because the range of an open-subscheme inclusion is that open.
   - Hence both sides of the n = 0 statement are unchanged when r is replaced by r*a, and the equality follows from the n > 0 case.

4. Sanity check on points: the chart map sends a point to the preimage of the corresponding homogeneous prime under f. So r lies in the image prime iff f r lies in the original prime, for any r. The statement therefore holds without positivity.

So `hn` can be dropped. Only `hr`'s grading and the other hypotheses are kept. `hr` is not reported, since removing it would need a pointwise argument I did not verify.

### [`finiteGroupPresentation_iff_compact_totallyDisconnected`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/FiniteGroupCharacterization.lean#L198-L214) — `formal-frontier-0200`

Snippet: `samples/formal-frontier/formal-frontier-0200.lean`

- `[T2Space G]` (theorem): The statement mentions only FiniteGroupPresentation G (which needs Group and TopologicalSpace), CompactSpace G and TotallyDisconnectedSpace G, so T2Space is not needed to elaborate it. The forward direction never uses it: it only transports compactness and total disconnectedness along the homeomorphism P.equiv.symm. The reverse direction uses it only through `ProfiniteGrp.of G`, whose signature is `[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]` (Mathlib's docstring says Hausdorff can be omitted for this reason). Mathlib's `TotallyDisconnectedSpace.t1Space` gives T1 from total disconnectedness. `IsTopologicalGroup.regularSpace` gives regularity. T1 gives T0, so `instT3Space` applies, and `T3Space.t25Space` then `T25Space.t2Space` give T2Space. So the theorem remains true and provable with the same proof after deleting `[T2Space G]`.

### [`AlgebraicGeometry.Scheme.Hom.ker_radical_of_isReduced_source`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L154-L160) — `formal-frontier-0232`

Snippet: `samples/formal-frontier/formal-frontier-0232.lean`

- `[QuasiCompact f]` (theorem): QuasiCompact f is only used to rewrite `f.ker.ideal U` to `RingHom.ker (f.app U).hom` by `Hom.ker_apply`. The statement is still true without it, and the proof can avoid that lemma. `f.ker` is `ofIdeals (fun U ↦ RingHom.ker (f.app U).hom)`, so `f.ker.radical ≤ f.ker` follows from `le_ofIdeals_iff` (Galois connection, `I ≤ ofIdeals J ↔ I.ideal ≤ J`). It then suffices to show `(f.ker.ideal U).radical ≤ RingHom.ker (f.app U).hom` for each affine open U. By `Hom.ideal_ker_le` (no QuasiCompact needed), `f.ker.ideal U ≤ RingHom.ker (f.app U).hom`. The radical of that kernel is the kernel itself, because the kernel of a ring hom into the reduced ring Γ(X, f⁻¹U) is radical, which is exactly what `Ideal.isRadical_bot.comap` shows in the current proof. The reverse inequality `f.ker ≤ f.ker.radical` is `Scheme.IdealSheafData.le_radical`, and `radical_ideal` gives `radical.ideal U = (I.ideal U).radical`. I checked these in Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean. So the conclusion holds for any f with reduced source.

### [`AlgebraicGeometry.iInf_ker_eq_vanishingIdeal_iSup_closure_range`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L176-L185) — `formal-frontier-0233`

Snippet: `samples/formal-frontier/formal-frontier-0233.lean`

- `[∀ j, QuasiCompact (f j)]` (theorem): The statement is still true without quasi-compactness, but the proof has to change. In Mathlib, `Scheme.Hom.ker f` is defined as `ofIdeals (fun U ↦ RingHom.ker (f.app U).hom)`, the largest ideal sheaf contained in the componentwise kernels. QuasiCompact is only used to identify `f.ker.ideal U` with `RingHom.ker (f.app U)` (`Hom.ker_apply`) and to get `Hom.support_ker`. For each j, `(f j).ker = vanishingIdeal (closure (range (f j)))` holds for any morphism from a reduced scheme. The ≤ direction does not need QC: `Hom.range_subset_ker_support` has no QC hypothesis, and closedness of the support gives `closure (range f) ≤ f.ker.support`. So `f.ker ≤ vanishingIdeal f.ker.support ≤ vanishingIdeal (closure (range f))`, using `vanishingIdeal_support` (the vanishing ideal of the support is the radical, which is ≥ I) together with antitonicity of `vanishingIdeal`. For ≥, use `le_ofIdeals_iff` to reduce to showing that every `s` in `(vanishingIdeal (closure (range f))).ideal U` satisfies `f.app U s = 0`. Such an `s` lies in every prime `p` of Γ(Y,U) whose point lies in the closure of the range. For each `x ∈ f⁻¹U`, `f x` lies in the range, so `x ∉ basicOpen (f.app U s) = f⁻¹(basicOpen s)`. Hence `basicOpen (f.app U s) = ⊥`, and since X is reduced, `f.app U s = 0`. Taking the infimum over j then goes through exactly as in the existing proof, via `vanishingIdeal_iSup`. IsReduced is genuinely needed: for the identity on a non-reduced scheme the kernel is ⊥ but the vanishing ideal of ⊤ is the nilradical.

### [`MvPowerSeries.existsUnique_firstVariable_division_of_scalar_top`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableDivision.lean#L112-L132) — `formal-frontier-0285`

Snippet: `samples/formal-frontier/formal-frontier-0285.lean`

- `(ha : a ≠ 0)` (theorem): The hypothesis `ha` is only passed to the lower-level lemma (`existsUnique_firstVariable_division_of_leadingExponent`, which forwards it to `existsUnique_restricted_primitive_singleton_division`). The statement itself is still true when a = 0.

Suppose a = 0. Then `hrad` says the radical of span{0} = ⊥ equals the maximal ideal. In a domain that radical is ⊥, so the maximal ideal is ⊥ and V is a field. In that case I = ⊥ and I^0 = ⊤. For k ≥ 1, I^k = ⊥. So `IsAdicallyRestricted` says exactly that only finitely many coefficients are nonzero (the k = 1 condition). Hence `adicallyRestrictedSubring` is the ordinary polynomial ring `MvPolynomial` over V, both in `Fin (n+1)` and in `Fin n` variables.

The residue map V → V/⊥ is a bijection, so `htop` and `hc` say that f, viewed as a polynomial in x0 over the polynomials in x1..xn, has degree d and a nonzero constant top coefficient. That is, f is a unit multiple of a polynomial monic in x0. Division by it gives unique q and r = polynomialRestrictedFinFirst P with deg_x0 P < d (d = 0 forces P = 0, which the `WithBot` degree bound allows). Mathlib has this over the first-variable polynomial ring (`Polynomial.divModByMonic` / `modByMonic`, after scaling by the unit, with the uniqueness lemma, transported through `MvPolynomial.finSuccEquiv`). So the existence and uniqueness conclusion holds with no `a ≠ 0`.

The proof would change as follows. Split on a = 0. If a ≠ 0, use the current argument. If a = 0, use the field and polynomial division argument above. I checked the degenerate cases d = 0 and n = 0, and neither breaks the argument. I did not write the a = 0 proof out in Lean.

