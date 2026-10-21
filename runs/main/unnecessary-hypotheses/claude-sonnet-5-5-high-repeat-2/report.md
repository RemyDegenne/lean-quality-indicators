# unnecessary-hypotheses: run `main`, judge `claude-sonnet-5-5-high-repeat-2`

| Library | Sampled | Judged | Flagged | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|
| Mathlib | 1000 | 300 | 7 | 2.3% | 1.1%–4.7% | $5.10 |
| Tau Ceti | 1000 | 300 | 10 | 3.3% | 1.8%–6.0% | $11.29 |
| Lean Pool | 1000 | 300 | 42 | 14.0% | 10.5%–18.4% | $10.65 |
| FLT (Anthropic) | 1000 | 300 | 54 | 18.0% | 14.1%–22.7% | $15.19 |
| Formal Frontier | 1000 | 300 | 11 | 3.7% | 2.1%–6.4% | $10.95 |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (7 flagged)

### [`RatFunc.Luroth.Φ_natDegree_eq_φ_natDegree`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/RatFunc/Luroth.lean#L182-L185) — `mathlib-0077`

Snippet: `samples/mathlib/mathlib-0077.lean`

- `(h : E ≠ ⊥)` (theorem): The statement `(Φ E).natDegree = (φ E).natDegree` also holds when E = ⊥. In that case `E` is the image of `K`, so `X` is transcendental over `E`. Any polynomial over `E` that kills `X` pulls back to a polynomial over `K` with the same evaluation, because `K → ⊥` is surjective. So `X` is not integral over `E`, and `φ E = minpoly E X = 0` by `minpoly.eq_zero`. Then `(φ E).map _ = 0`, and `Φ' E = integerNormalization … 0 = 0` (`IsFractionRing.integerNormalization_eq_zero_iff`). Therefore `Φ E = (0 : K[X][Y]).primPart = 1` by `Polynomial.primPart_zero`, whose docstring says `p = 0 → p.primPart = 1`. Both natDegrees are 0, so the equality holds. A proof case-splits on `E = ⊥`: the `E ≠ ⊥` case is the existing proof, and the `E = ⊥` case is the computation above. The statement itself needs nothing from `h`: `Φ` and `φ` are defined without it.

### [`Module.Basis.toMatrix_mulVec_repr`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Matrix/Basis.lean#L231-L236) — `mathlib-0083`

Snippet: `samples/mathlib/mathlib-0083.lean`

- `[Finite ι']` (theorem): The statement doesn't need Finite ι'. Here `b'.toMatrix b : Matrix ι' ι R` is defined by `fun i j ↦ b'.repr (b j) i`, as the definition at line 51 of Basis.lean shows. The product `*ᵥ` sums only over the column index ι, which is covered by the variable `[Fintype ι]`. No finiteness of the row index ι' is used. For each i : ι', the i-th entry of the left side is `∑ j, b'.repr (b j) i * b.repr m j`. This equals `b'.repr (∑ j, b.repr m j • b j) i`, which is `b'.repr m i` by `b.sum_repr`. The argument works for any ι', including empty or infinite ι'. The proof can be done directly with `ext i; simp [Matrix.mulVec, dotProduct, Basis.toMatrix_apply, ...]`, rewriting with `map_sum`, `map_smul` and `Basis.sum_repr`. This is the same kind of computation as line 105 of the file, which is `simp_rw [e.toMatrix_apply, e.sum_repr]`. The current proof's detour through `LinearMap.toMatrix` is the only reason it needs Finite ι' (and the `Fintype ι'` it extracts from it).

### [`MeasureTheory.projectiveFamilyContent_mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean#L134-L137) — `mathlib-0116`

Snippet: `samples/mathlib/mathlib-0116.lean`

- `(hs : s ∈ measurableCylinders α)` (theorem): hs can be dropped. `projectiveFamilyContent_eq` (proved by `rfl`) says `projectiveFamilyContent hP s = projectiveFamilyFun P s` for every `s`, with no membership assumption. By definition `projectiveFamilyFun P s = if hs : s ∈ measurableCylinders α then ... else 0`. Split on `s ∈ measurableCylinders α`. If it holds, the existing proof `addContent_mono isSetSemiring_measurableCylinders hs ht hst` applies unchanged. If it fails, `projectiveFamilyFun P s = 0` (`dif_neg`), so the left side is 0 and `zero_le` closes the goal. So the statement stays true without hs. By contrast, `ht` cannot be dropped: if `t` is not a measurable cylinder the right side is 0 while the left side can be positive.

### [`WeierstrassCurve.preΨ_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean#L314-L318) — `mathlib-0123`

Snippet: `samples/mathlib/mathlib-0123.lean`

- `[Nontrivial R]` (theorem): The hypothesis h : (n : R) ≠ 0 already forces R to be nontrivial. In a trivial ring every element equals 0, so (n : R) = 0 and h would be false. Formally, `nontrivial_of_ne (n : R) 0 h : Nontrivial R`. The statement `W.preΨ n ≠ 0` does not need Nontrivial R to elaborate. So the theorem stays true after deleting the binder, and the trivial-ring case is vacuous. The proof changes by adding `haveI : Nontrivial R := nontrivial_of_ne _ _ h` at the start, before the induction. The existing proof, which uses `W.preΨ'_ne_zero` and the induction hypothesis, then goes through. I did not open the source of `preΨ'_ne_zero`. I am assuming it needs only `[Nontrivial R]` and a cast-nonzero hypothesis, as its use in the proof suggests.

### [`AdicCompletion.tensor_map_id_left_injective_of_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean#L367-L373) — `mathlib-0139`

Snippet: `samples/mathlib/mathlib-0139.lean`

- `[Module.Finite R M]` (variable): The statement (injectivity of id ⊗ f : AdicCompletion I R ⊗[R] M → AdicCompletion I R ⊗[R] N) does not mention finiteness. It is true without it, since for Noetherian R the adic completion AdicCompletion I R is flat over R, which is exactly the instance `flat_of_isNoetherian` in the same file. Flatness gives that `lTensor (AdicCompletion I R) f` is injective for any injective f, and `AlgebraTensorModule.map LinearMap.id f` has the same underlying function as that lTensor. The finiteness is used only in this proof, via `tensor_map_id_left_eq_map` and `ofTensorProductEquivOfFiniteNoetherian`. It is needed only to prove flatness, and for that only the case M = an ideal J (finitely generated since R is Noetherian) and N = R is required. So the lemma can be restated for finite modules, used for flatness, and the general version follows from flatness by `Module.Flat.lTensor_preserves_injective_linearMap`. The proof is reorganised but the statement stays true. The hypothesis is also deletable on its own: with only [Module.Finite R N] dropped or kept, the flatness argument still applies.
- `[Module.Finite R N]` (variable): Same reasoning as for `[Module.Finite R M]`. Neither module's finiteness appears in the statement. The result follows from flatness of AdicCompletion I R over the Noetherian ring R, which gives injectivity of `lTensor (AdicCompletion I R) f` for every injective f between arbitrary R-modules. Finiteness is needed only for the proof via the tensor-product equivalence, which is used to establish flatness in the first place (with M an ideal and N = R). Dropping it is independent of dropping the finiteness of M, and both can be dropped together.

### [`continuous_parametric_integral_of_continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/Bochner/Set.lean#L1121-L1139) — `mathlib-0190`

Snippet: `samples/mathlib/mathlib-0190.lean`

- `[FirstCountableTopology X]` (theorem): First countability of X is only used because the proof applies continuousAt_of_dominated, which needs 𝓝 x₀ to be countably generated. The theorem is true without it, by a direct epsilon argument. Fix x₀ and ε>0. By continuity of f.uncurry and compactness of s (tube lemma), there is a neighbourhood V of x₀ with ‖f x y − f x₀ y‖ < ε for all x ∈ V and y ∈ s. Each f x is continuous, so it is bounded on s and, via SecondCountableTopologyEither Y E, AE-strongly measurable, hence integrable on s because μ s < ∞ (s compact, μ locally finite). The set {y | ‖f x y − f x₀ y‖ ≤ ε} is closed, hence measurable by OpensMeasurableSpace Y, and contains s, so the bound holds μ.restrict s-a.e. Hence ‖∫_s f x − ∫_s f x₀‖ ≤ ε·μ(s).toReal for x ∈ V, which gives continuity at x₀. Nothing degenerates when s is empty or has measure zero. The two removable hypotheses (this one and LocallyCompactSpace X) can each be removed alone and also both together.
- `[LocallyCompactSpace X]` (theorem): Local compactness of X is only used to get a compact neighbourhood U of x₀, which supplies the uniform bound M. The tube-lemma argument gives a neighbourhood V of x₀ on which sup over y∈s of ‖f x y − f x₀ y‖ < ε, using only compactness of s and continuity of f.uncurry. No local compactness of X is needed for this. The ε·μ(s) estimate then yields continuity at x₀ exactly as described for FirstCountableTopology X. Measurability and integrability come from SecondCountableTopologyEither Y E, IsLocallyFiniteMeasure μ, hs and OpensMeasurableSpace Y, which stay. The statement is therefore true without it. It can be removed on its own and also together with FirstCountableTopology X.

### [`MeasureTheory.Measure.prod_smul_left`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Prod.lean#L877-L881) — `mathlib-0275`

Snippet: `samples/mathlib/mathlib-0275.lean`

- `[hν : SFinite ν]` (variable): `Measure.prod μ ν` is defined for arbitrary ν. By its definition in Prod.lean it is `if SFinite ν then bind μ (fun x => map (Prod.mk x) ν) else 0`. The statement therefore elaborates without `SFinite ν`. If ν is not s-finite, both `(c • μ).prod ν` and `μ.prod ν` are `0`, so the goal reads `0 = c • 0`, which holds because scalar multiplication preserves zero on `Measure`. If ν is s-finite, the existing proof applies unchanged. The proof is `by_cases h : SFinite ν`, with the existing proof in the positive case. In the negative case, unfold `Measure.prod`, rewrite with `h`, and close with `smul_zero`. The other variable `[SFinite μ]` is not an argument, because the theorem's own `{μ : Measure α}` binder shadows the variable μ. So `hν` is the only s-finite hypothesis the theorem takes, and it can be deleted.


## Tau Ceti (10 flagged)

### [`CongruenceSubgroup.Gamma0_index_mul_prod_primeFactors`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/ModularForms/CongruenceSubgroups/Basic.lean#L952-L963) — `tauceti-0001`

Snippet: `samples/tauceti/tauceti-0001.lean`

- `(hN : N ≠ 0)` (theorem): The statement is still true for N = 0. Then primeFactors 0 = ∅, so both products are 1 and the claim reads (Gamma0 0).index = 0. Γ₀(0) has infinite index, and Subgroup.index is 0 for infinite index. A short proof: for every prime p, Gamma0 0 ≤ Gamma0 p, since c ≡ 0 mod 0 means c = 0, which is 0 mod p. By Subgroup.index_dvd_of_le, (Gamma0 p).index ∣ (Gamma0 0).index. The file's Gamma0_prime_index gives (Gamma0 p).index = p + 1. If (Gamma0 0).index were nonzero, then p + 1 ≤ (Gamma0 0).index for all primes p. That is impossible, because there are arbitrarily large primes (Nat.exists_infinite_primes). So the index is 0 and the N = 0 case holds. The nonzero case still goes through the existing proof, so the hypothesis can be dropped by case-splitting on N = 0. (The outer `variable {N : ℕ}` is shadowed and is not an argument.)

### [`HeckeRing.GLn.posDetInt_le_commensurator`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/HeckeRing/GLn/Basic.lean#L712-L717) — `tauceti-0020`

Snippet: `samples/tauceti/tauceti-0020.lean`

- `[NeZero n]` (variable): The statement only uses `posDetInt n`, `SLnZ n` and `commensurator`. `SLnZ` and `posDetInt` are defined (lines 74 and 257) before `variable [NeZero n]` at line 460 and don't need the instance. The instance is a theorem argument only because it is instance-implicit and mentions `n`. The theorem is still true without it. For n ≥ 1 the instance can be rebuilt as `⟨Nat.pos_iff_ne_zero.mp h⟩` (or `⟨h.ne'⟩`), so the existing proof via `mem_commensurator_of_hasIntEntries` goes through (that lemma uses NeZero only in `conj_mat_det_one`, through `NeZero.pos n`). For n = 0, `GL (Fin 0) ℚ` is a subsingleton group (units of a subsingleton matrix type), so every `g` equals 1 and lies in the commensurator, because `one_mem` holds in any subgroup. So the proof can split on `n = 0` versus `0 < n`. Use `omit [NeZero n] in`, then `rcases Nat.eq_zero_or_pos n`. In the positive case, `haveI : NeZero n := ⟨…⟩` followed by the current proof. In the zero case, `Subsingleton.elim` gives `g = 1`, then use `one_mem`. The degenerate n = 0 case therefore holds, and the hypothesis can be deleted.

### [`TauCeti.Nat.gcd_eq_gcd_ordCompl_mul_pow_min`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Data/Nat/Factorization/GcdSplit.lean#L56-L71) — `tauceti-0078`

Snippet: `samples/tauceti/tauceti-0078.lean`

- `(hp : p.Prime)` (theorem): The statement is still true when p is not prime. In that case `Nat.factorization_eq_zero_of_not_prime` gives `m.factorization p = 0` and `n.factorization p = 0`. So `ordCompl[p] m = m / p^0 = m`, `ordCompl[p] n = n`, and `min 0 0 = 0`. The right side becomes `gcd m n * p^0 = gcd m n`, which is the left side. This covers p = 0 and p = 1 as well. The proof splits with `by_cases hp : p.Prime`. The prime case is the existing proof. The non-prime case is `simp [Nat.factorization_eq_zero_of_not_prime _ hp]`. The other two hypotheses cannot be dropped, because for prime p, m = 0 and n = p make the statement false (left side p, right side 1). The symmetric case, n = 0 and m = p, fails the same way.

### [`LipschitzWith.ae_finite_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Function/AreaFormula/Real.lean#L119-L126) — `tauceti-0115`

Snippet: `samples/tauceti/tauceti-0115.lean`

- `(hs : NullMeasurableSet s volume)` (theorem): The result holds for arbitrary s. Let t := toMeasurable volume s, which is measurable (hence null-measurable) and contains s (subset_toMeasurable). Since volume on the finite-dimensional inner product space U is s-finite (it is an add Haar measure, hence σ-finite), Measure.restrict_toMeasurable_of_sfinite (Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean) gives volume.restrict t = volume.restrict s. As IntegrableOn g s is Integrable g (volume.restrict s), hint for s transfers verbatim to IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet) t. Applying the existing proof (ae_summable_fiber with hs instantiated at t, then Finite.of_summable_const) to t gives ∀ᵐ y ∂μHE[finrank ℝ U], (t ∩ f ⁻¹' {y}).Finite. Then s ∩ f ⁻¹' {y} ⊆ t ∩ f ⁻¹' {y} gives finiteness for s via Set.Finite.subset. So the statement stays true and provable after deleting hs. I could not run Lean, so this proof sketch is unchecked.

### [`TauCeti.exists_zmultiples_eq_top_groupCohomology_two_res_padicCompletionUnits`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/Padics/MultiplicativeCompletion/Cohomology.lean#L195-L206) — `tauceti-0118`

Snippet: `samples/tauceti/tauceti-0118.lean`

- `[CharZero K]` (variable): The statement only involves `padicCompletionUnitsRepresentation p L K`, `Rep.res`, `groupCohomology`, `Nat.card` and `padicValNat`. In Basic.lean, `padicCompletionUnitsRepresentation` needs only `Fact p.Prime`, `CommSemiring L`, `CommSemiring K` and `Algebra K L`. So `CharZero K` is not needed to elaborate the statement. `[CharZero K]` is an instance-implicit variable that is pulled in only because it mentions `K`.

It is also implied by the other hypotheses. `K` is a field, so `algebraMap K L` is injective, and `[CharZero L]` is already a hypothesis. `RingHom.charZero_iff (algebraMap K L).injective` gives `CharZero L ↔ CharZero K`, so `CharZero K` follows. Mathlib uses this lemma the same way, for example in Padics/Complex.lean: `(RingHom.charZero_iff (algebraMap ℚ_[p] ℂ_[p]).injective).mp inferInstance`.

The proof goes through `groupCohomology_res_padicCompletionUnits` and `groupCohomology_of_le`, which use `CharZero K` through instances, for example in `strictCohomologicalDimensionAt_galSeparableClosure_eq_two (K := K)`. To delete the hypothesis, add `have : CharZero K := (RingHom.charZero_iff (algebraMap K L).injective).mp inferInstance` at the start of the proof. The helper lemma would need the same line, or the instance could be omitted from the theorem with `omit [CharZero K] in` and the line added in the proof. The theorem therefore stays true and provable. I did not check how the helper lemmas consume the instance, but the derived instance is the same proposition, so any use of it is covered.

### [`Matrix.ProjectiveSpecialLinearGroup.isParabolic_inv_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/ProjectiveSpecialLinearGroup/FinTwo.lean#L103-L117) — `tauceti-0134`

Snippet: `samples/tauceti/tauceti-0134.lean`

- `[NoZeroDivisors R]` (variable): The statement does not need it: `IsParabolic` for `PSL(2,R)` is defined (line 59) before `variable [NoZeroDivisors R]`, as `∃ a : SL(2,R), (a : PSL(2,R)) = g ∧ (a : GL (Fin 2) R).IsParabolic`, with `Matrix.IsParabolic m := m ∉ Set.range (scalar _) ∧ m.discr = 0`. The theorem stays true over any CommRing. For `a : SL(2,R)`, `a⁻¹` has matrix `adjugate a` (entries d, -b, -c, a). It is scalar iff b = 0, c = 0 and a₀₀ = a₁₁, exactly as for `a`, since -b = 0 ↔ b = 0, with no cancellation needed. Its trace and determinant equal those of `a`, so its discriminant is equal. Hence `a⁻¹` is parabolic iff `a` is, which is what the existing `simp only [... hscalar, discr_fin_two, adjugate_fin_two ...]` computation shows; none of its steps use NoZeroDivisors. Proof without the hypothesis: unfold `IsParabolic` directly. For →, a witness `a` with `(a : PSL) = g⁻¹` gives the witness `a⁻¹` for `g` via `QuotientGroup.mk_inv`. For ←, a witness `a` for `g` gives `a⁻¹` for `g⁻¹`. The only use of the hypothesis in the current proof is `isParabolic_mk_iff`, which requires it, so that rewrite is replaced by this direct unfolding. Deleting it would use `omit [NoZeroDivisors R] in`, as other lemmas in this file do.

### [`MeasureTheory.Measure.rnDeriv_mul_measure_singleton`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Measure/Decomposition/Lebesgue.lean#L46-L58) — `tauceti-0170`

Snippet: `samples/tauceti/tauceti-0170.lean`

- `[MeasurableSingletonClass α]` (variable): The statement only uses `μ.rnDeriv ν x`, `ν {x}` and `μ {x}`, so it elaborates without this instance. `{x}` need not be measurable, in which case `ν {x}` is the outer-measure value. The theorem stays true without the instance, but the proof has to change, because the current one uses `measurableSet_singleton`.

Let f = μ.rnDeriv ν (measurable) and N = the null set of `mutuallySingular_singularPart μ ν` (measurable, ν N = 0, singularPart (Nᶜ) = 0). Let S = toMeasurable ν {x} and T = toMeasurable μ {x}, so ν S = ν {x} and μ T = μ {x}. This uses `measure_toMeasurable`.

1. Since hx gives ν {x} ≠ 0, x ∉ N. Otherwise {x} ⊆ N and ν {x} ≤ ν N = 0.
2. Put S'' = S ∩ T ∩ {f = f x} ∩ Nᶜ. It is measurable and contains x. The set {f = f x} is measurable because f is.
3. By monotonicity, ν S'' = ν {x} and μ S'' = μ {x}.
4. Write μ = singularPart + withDensity f ν, as in the existing proof. The singular part vanishes on S'' ⊆ Nᶜ. Since f ≡ f x on S'', `withDensity_apply` and `setLIntegral_const` give withDensity f ν S'' = f x * ν S''.
5. Hence μ {x} = f x * ν {x}.

The argument also works when ν {x} = ∞. The other hypotheses are genuinely needed: hx is needed because ν = 0 and μ = dirac x make the claim false, and HaveLebesgueDecomposition is needed because otherwise rnDeriv = 0 and singularPart = 0.

### [`TauCeti.cwEulerChar_preimage_of_card_fiber`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Cellular/EulerCharacteristic/Covering.lean#L75-L88) — `tauceti-0231`

Snippet: `samples/tauceti/tauceti-0231.lean`

- `(hfin : ∀ b, Finite ↥(p ⁻¹' {b}))` (variable): The statement does not mention hfin; it is an argument only because of `include hp hfin`. It is used only in the proof, via `nat_card_cell_preimage_of_card_fiber` → `nat_card_cell_preimage` → `Nat.card_sigma`, which needs each fibre to be finite. The hypothesis `hd` (every fibre over a point of C has `Nat.card = d`) already gives what the proof needs. Per dimension n, we need `Nat.card (cell (p⁻¹' C) n) = d * Nat.card (cell C n)`, and `cell (p⁻¹' C) n` is definitionally `Σ i : cell C n, p⁻¹' {map n i 0}` (`cellPreimageEquiv` is `Equiv.refl`). `cell C n` is finite, from `FiniteType.finite_cell`. Case d ≠ 0: each fibre over a centre has `Nat.card = d ≠ 0`, hence is finite (`Nat.finite_of_card_ne_zero`), so `Nat.card_sigma` applies and the sum is d·#cell. Case d = 0: the right side is 0. The left side is also 0. If all fibres over the centres are empty, the sigma type is empty. Otherwise some fibre is nonempty with `Nat.card = 0`, hence infinite, so the sigma type is infinite and its `Nat.card` is 0. Either way `Nat.card = 0`. The rest of the proof (the vanishing bound `hN'`, `cwEulerChar_eq_sum_range`, `Finset.sum_congr`) never uses hfin. So the theorem remains true and provable with `omit hfin in`, replacing the call to `nat_card_cell_preimage_of_card_fiber` by this short case analysis. Deleting only hfin from this theorem is fine; the sibling lemmas that use it are not affected.

### [`TauCeti.schwarzChristoffelEdgeAngle_comp_strictMono`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/GlobalTurning.lean#L114-L125) — `tauceti-0238`

Snippet: `samples/tauceti/tauceti-0238.lean`

- `[LocallyFiniteOrder ι]` (variable): The statement only uses `Fintype ι` (for the sum in `schwarzChristoffelEdgeAngle`) and `LinearOrder ι` (for `StrictMono`). It never mentions `LocallyFiniteOrder ι`. The instance is redundant, because every finite linear order is locally finite. Mathlib has `Fintype.toLocallyFiniteOrder [Fintype α] [DecidableLT α] [DecidableLE α] : LocallyFiniteOrder α`. It is a non-instance abbrev in Mathlib/Order/Interval/Finset/Defs.lean, and `LinearOrder` supplies the decidability instances. So the theorem stays true after deleting the argument, for example with `omit [LocallyFiniteOrder ι] in`. The proof changes only by adding `letI : LocallyFiniteOrder ι := Fintype.toLocallyFiniteOrder` at the start. The rest is unchanged, since `schwarzChristoffelEdgeAngle_sub_eq_neg_pi_mul_sum_Ioc` and `Finset.Ioc` then use that local instance. The `Finset.sum_neg` step needs only nonemptiness of `Ioc i j`, which comes from `j` itself. The empty-type case is not a problem, since `StrictMono` over an empty type is trivial.

### [`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_of_isCompact`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/PDE/Regularity/HolderContinuity.lean#L238-L258) — `tauceti-0281`

Snippet: `samples/tauceti/tauceti-0281.lean`

- `[Nonempty ι]` (theorem): The statement stays true without `[Nonempty ι]`. If ι is empty, `EuclideanSpace ℝ ι` is `WithLp 2 (ι → ℝ)`. `ι → ℝ` is `Unique` when `ι` is empty, and `WithLp.instUnique` (Mathlib/Analysis/Normed/Lp/WithLp.lean) transfers this, so the space is a single point. Any `K` in it is then a subsingleton. Take `α = 1`, which satisfies `0 < α ≤ 1`, and `C = 0`. `HolderOnWith C α f K` asks for `edist (f x) (f y) ≤ C * edist x y ^ α` for `x, y ∈ K`. Here `x = y`, so the left side is `0` and the inequality holds. So the proof can start with `rcases isEmpty_or_nonempty ι`. The empty case uses this argument, and the nonempty case uses the existing proof via `exists_holderOnWith_preciseRepresentative_of_isCompact_drift`. The statement involves no other `Nonempty ι`-dependent element, since `α` is chosen before the universally quantified data.


## Lean Pool (42 flagged)

### [`ViscositySolns.exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/ViscositySolns/Analysis/SemiconvexJensen/Aleksandrov/JetCalculus/Strictification/StrictifiedObjective.lean#L337-L370) — `lean-pool-0000`

Snippet: `samples/lean-pool/lean-pool-0000.lean`

- `(hr : 0 <= r)` (theorem): The conclusion is only an existence statement about `CoordinateSemiconvexOn lambda (Metric.closedBall 0 r) f`. That definition begins `∀ x, x ∈ C -> ∀ y, y ∈ C -> ...`. If r < 0, `Metric.closedBall 0 r` is empty, so the statement holds vacuously for any lambda, for example 0. If 0 ≤ r, the existing proof applies unchanged, because it only uses `hr` when it is available. So the proof is `by_cases hr : 0 ≤ r`. In the positive case it uses the current argument. In the negative case it takes `⟨0, fun x hx => ?_⟩` and gets a contradiction from `hx : ‖x‖ ≤ r` (via `mem_closedBall_zero_iff`) with `norm_nonneg x` and `r < 0`. The theorem is therefore true and provable without `hr`. `r` still appears in the conclusion, so nothing else in the statement needs to change.

### [`NavierStokes.ParticularWaveBounds.pressure_class`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/ParticularWaveBounds.lean#L1371-L1389) — `lean-pool-0009`

Snippet: `samples/lean-pool/lean-pool-0009.lean`

- `(hupper : ∀ n x, x ∈ s.domain → ‖N n x‖ ≤ M)` (theorem): The conclusion is still true without the upper bound, but the current proof does need changing. The only use of `hupper` is in `normalInverse_unweighted` → `PolynomialJets.inv` → `PolynomialJets.compact_comp`. There it is used to put the values of `‖N n x‖^2` in the compact set `closedBall 0 M ∩ {b ≤ |r|}`, so that the fixed outer function `u ↦ u⁻¹` has bounded derivatives. That compactness is used only to bound `iteratedFDeriv ℝ k (·⁻¹)` at the points `f i x`, via `compact_jet_bound`. Dropping `hupper` does not weaken the polynomial-jet bound that `PolynomialJets` gives for `N`: it is `C * scale^m`, and this is non-uniform in the index anyway. The needed bound on the outer function holds without any upper bound. For `u ≥ b^2` (from `hlower` and `hb`), `|d^k(u⁻¹)| = k!/u^(k+1) ≤ k!/b^(2(k+1))`, which is a global bound on the whole ray `[b^2, ∞)`. The remaining steps use no compactness: `norm_iteratedFDerivWithin_comp_le` and the polynomial bound on `‖N‖^2` from `hN.norm_sq`. Replace `compact_jet_bound` by this explicit bound on `[b^2, ∞)`, and apply `compact_comp` with that bound in place of compactness. Alternatively, compose with a smooth function equal to `u⁻¹` on `[b^2, ∞)` that has globally bounded derivatives. The rest of `pressure_class` does not use `M` or `hupper`: `polynomialJets_unweighted hN`, `real_inner_class`, `hA`, `hNdot`, and the `Complex.I / frequency` step with `hfreq`. Degenerate cases are fine: `hb : 0 < b` with `hlower` keeps `‖N‖` away from 0, so there is no division-by-zero junk issue. Once `hupper` is gone, `M` is mentioned nowhere else and can be dropped as well.

### [`CKN.Leray.integral_ae_eq_integral_jointRep`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegularisedJointRep.lean#L247-L298) — `lean-pool-0024`

Snippet: `samples/lean-pool/lean-pool-0024.lean`

- `[CompleteSpace E]` (variable): Redundant given [InnerProductSpace ℂ E] and [FiniteDimensional ℂ E]. Instances NormedSpace.complexToReal (NormedSpace ℝ E) and FiniteDimensional.complexToReal (FiniteDimensional ℝ E) feed FiniteDimensional.proper_real (priority 900), which gives ProperSpace E, hence CompleteSpace E, and so CompleteSpace (Lp E 2 μ) needed for the Bochner integral in the statement. So the statement still elaborates and is the same true statement; the proof is unchanged, since every use of completeness (Lp integral/integral_inner) finds the instance via this chain. stdOrthonormalBasis only needs FiniteDimensional.

### [`IsoGraph.Canon.splitCell_tr_general`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Equivariance.lean#L3331-L3342) — `lean-pool-0028`

Snippet: `samples/lean-pool/lean-pool-0028.lean`

- `(hw : writeFrom block c block.size 0 st.lab st.pos = (lab, pos))` (theorem): The conclusion `(splitCell cnt c st).tr = tr` only depends on `tr` via `hbd`. In `splitCell` (Algorithm.lean:376), `boundsFrom` is called with `ks`, `sizes`, `st.cst`, `st.cen`, `c` and `mixN st.tr c`. It does not use `lab`, `pos` or `block`, and `sizes` is fixed by `ho`. `hw` only introduces `lab` and `pos`, and neither appears in the conclusion or in `hbd`. Without `hw` (and the implicit `lab`, `pos`), the statement is still true. The proof obtains the write result as `obtain ⟨lab, pos, hw⟩ : ∃ lab pos, writeFrom block c block.size 0 st.lab st.pos = (lab, pos) := ⟨_, _, rfl⟩`, then runs the same `rw [splitCell_eq_general hb h1 h2 ho hsc hw hbd]`. This is the same trick `splitCell_bc` uses for `hb`. `hw` can be deleted on its own.
- `(hsc : scatterFrom st.lab cnt st.cen[c]! (st.cen[c]! - c) c (Array.replicate (st.cen[c]! - c) 0) bc1 = (block, bc2))` (theorem): `tr` is computed by `boundsFrom` from `ks0`, `sizes`, `st.cst`, `st.cen`, `c` and `st.tr`. None of these depend on the scatter result `block, bc2`; `block` and `bc2` feed only `lab`, `pos` and `bc`, which the conclusion never mentions. Dropping `hsc` leaves `block` unconstrained, but only `hw` mentions it, and the conclusion is independent of it. The proof can recover both facts with `∃ block bc2, scatterFrom … = (block, bc2) := ⟨_, _, rfl⟩` and similarly for `hw`, then apply `splitCell_eq_general`. `hsc` can be deleted on its own, and it can also be deleted together with `hw`. In that case the proof obtains both by `⟨_, _, rfl⟩`, which is even simpler. The other hypotheses (`hb`, `h1`, `h2`, `ho`, `hbd`) are needed.

### [`ESS.buCut_gradient_absorption`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUShortGradient.lean#L28-L102) — `lean-pool-0033`

Snippet: `samples/lean-pool/lean-pool-0033.lean`

- `(hM : 0 ≤ M)` (theorem): hM follows from hderiv. Take j = 0 : Fin 3, which exists because Fin 3 is nonempty. Then 0 ≤ |spatialPartial (buCutScalar κ) 0 z| ≤ M, so 0 ≤ M. The proof can begin with `have hM : 0 ≤ M := (abs_nonneg _).trans (hderiv 0)`, and the rest is unchanged.
- `(hκ : 0 ≤ buCutScalar κ z)` (theorem): The statement stays true without hκ. Let ξ = buCutScalar κ z. If ξ ≥ 0, the existing proof applies unchanged. If ξ < 0, the left side ξ * sqrt(...) is ≤ 0, because the square root is nonnegative. The right side 3 * (sqrt(...) + M * ‖v z‖) is ≥ 0, using M ≥ 0 (derived from hderiv as above) and `vec3EuclideanNorm_nonneg`. So the inequality holds. A proof does `rcases le_or_gt 0 ξ`: the first case reuses the current argument, and the second case uses `mul_nonpos_of_nonpos_of_nonneg` (or nlinarith) with `Real.sqrt_nonneg`. The `abs_of_nonneg hκ` step is the only place hκ is used, and it is needed only in the ξ ≥ 0 case. The two hypotheses can be removed independently, and both can be removed together.

### [`IsoGraph.Canon.individualize_refines`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/IsoGraph/Canon/Progress.lean#L192-L202) — `lean-pool-0038`

Snippet: `samples/lean-pool/lean-pool-0038.lean`

- `(hv : v < n)` (theorem): The statement still holds without hv. Refines n q p only says: for i < n, p.cst[i]! = i → q.cst[i]! = i. If n = 0 this is vacuous. Otherwise, if v ≥ n, then since hp.posSize gives p.pos.size = n ≤ v, p.pos[v]! is the default 0. So the split cell is the one containing position 0, with c = p.cst[0]! ≤ 0 by hp.cstLe, so c = 0, and ec = p.cen[0]!. By individualize_cst_eq and setCstFrom_getElemD (which needs only ec ≤ p.cst.size, from hp.cenLe and hp.cstSize), the new cst[k]! is 1 if 1 ≤ k < ec, and p.cst[k]! otherwise. Suppose p.cst[i]! = i with 1 ≤ i < ec. Then hp.cellCst at index 0 gives p.cst[i]! = p.cst[0]! = 0, so i = 0, a contradiction. So the new cst[i]! = p.cst[i]! = i in every case. For v < n the existing proof applies unchanged. In the proof, hv is used only to build IndivData, so a case split on v < n replaces that step. The out-of-range case is the short argument above, done directly with individualize_cst_eq and setCstFrom_getElemD. hp is still needed: for an arbitrary Part the cst array could have a cell start inside the split interval.

### [`TauCeti.DavisKahanExt.le_riccati_small_root_of_quadratic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Riccati/BoundedSharpEstimates.lean#L41-L89) — `lean-pool-0045`

Snippet: `samples/lean-pool/lean-pool-0045.lean`

- `(hd : 0 < d)` (theorem): hd is implied by hb : 0 ≤ b and hsmall : 2 * b < d, since d > 2b ≥ 0. Deleting it leaves the statement unchanged and true. In the proof, hd is used only in `hsumpos : 0 < d + 2 * b`, and `linarith` proves that from hb and hsmall (d + 2b > 4b ≥ 0). The later steps (hdiscpos, hden : 0 < d + s, and so on) use only hsumpos, hsmall, hb and s ≥ 0. If needed, `have hd : 0 < d := by linarith` can be added as the first line of the proof.

### [`NavierStokes.HeatedOutgoing.E_times_U`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/HeatedOutgoing.lean#L1197-L1206) — `lean-pool-0047`

Snippet: `samples/lean-pool/lean-pool-0047.lean`

- `(hX : 0 < X)` (theorem): hX is used only via heatE_times_U (heatE_before and U_after_switch). The statement is still true for X ≤ 0, with K = switchRadius F XR > 0 (switchRadius_pos). Definitions: heatE = OutgoingDilation.E * multiplier, multiplier = 1 + switch K X * (...), switch K X = sigma(Real.log (X/K)/(3/10)), and U F XR (X,eta) = F.U (X/XR, eta) = F.logU (Real.log (X/XR), eta). If X = 0, Real.log 0 = 0, so switch = sigma 0 = 0 (OutgoingSchedule.sigma_zero), the multiplier is 1, and heatE = OutgoingDilation.E. If X < 0 and -X ≤ K, Real.log_neg_eq_log gives Real.log (X/K) = Real.log ((-X)/K) ≤ 0, so switch = 0 and the multiplier is 1. If X < 0 and -X > K, then Real.log (X/XR) = Real.log ((-X)/XR) by Real.log_neg_eq_log and neg_div, so U F XR (X,eta) = U F XR (-X,eta) = 0 by U_after_switch at -X; both sides are then _ * 0 = 0. The patch part (correction_times_U_zero) takes no hypothesis on X. So the proof only needs heatE_times_U reproved by a case split on 0 < X, where the positive case is the existing proof. hXR is still needed (U_on_patch).

### [`EulerOrdinarySobolev.Evolution.gradient_logarithmic_envelope`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/OrdinaryEulerBKM.lean#L109-L141) — `lean-pool-0078`

Snippet: `samples/lean-pool/lean-pool-0078.lean`

- `(hC : 0 ≤ C)` (variable): hC follows from the other hypotheses. The theorem is stated for a given t : Icc 0 T, so hlog t is available. Write X = 1 + ‖(U.velocity t).toLp‖ + W t * log (exp 1 + tensorNorm 3 (U.velocity t)). Then U.gradientNormPath t ≤ C * X. The left side is ≥ 0 by `gradientNormPath_nonneg`, which is a norm (OrdinaryEulerGradientControl.lean line 416). X ≥ 1 > 0, for three reasons. First, ‖·‖ ≥ 0. Second, W t ≥ 0 by hW. Third, `tensorNorm_nonneg` gives exp 1 + tensorNorm 3 _ ≥ 1, so the log is ≥ 0 (`Real.log_nonneg`). Hence 0 ≤ C * X with X > 0, so 0 ≤ C (for example `nonneg_of_mul_nonneg_left`, or by_contra with nlinarith). Add `have hC : 0 ≤ C := ...` at the start of the proof and the rest is unchanged, because hC is only used in mul_le_mul_of_nonneg_left steps. The statement also does not need hC to elaborate: `logarithmicGronwallConstant C _` is defined for any real C. Delete it with `omit hC in`.

### [`NavierStokes.SignedCopyBounds.local_mul`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SignedCopyBounds.lean#L91-L97) — `lean-pool-0090`

Snippet: `samples/lean-pool/lean-pool-0090.lean`

- `(hw : ∀ n x, x ∈ s.domain → 0 ≤ w n x)` (theorem): The statement stays true without it, and it can be dropped together with `hv`. `local_mul` is `LocalJets.bilinear` (PeriodizedWaveBounds.lean:488) with `L = lsmul ℝ ℝ`. That proof uses `hw` and `hv` only through `majorant_nonneg`. That lemma is used to get `0 ≤ majorant s w α A p n x`, and likewise for `v`, as the `hA` and `hB` arguments of `bilinear_jet_at`. These nonnegativity facts follow from the bounds themselves. At any `x ∈ s.domain ∩ K n i`, `hf.bounds` with `j = 0` gives `0 ≤ ‖f n i x‖ ≤ majorant s w α A p n x`, so the majorant is nonnegative. The same holds for `g` and `v`. `bilinear_jet_at` is private. Its `hA` and `hB` are used only to multiply the inequalities `hbu` and `hbv`, and both can be replaced by `(norm_nonneg _).trans (hbu 0 (Nat.zero_le _))` and the analogue for `hbv`. The remaining steps use no sign of `w` or `v`. `majorant_mul` is an unconditional identity. The constant `‖L‖ * 2^m * A * B` is nonnegative because `A, B ≥ 0` come from `hf.bounds` and `hg.bounds`. The conclusion's weight `w * v` appears only inside `majorant`. So the statement holds with no sign assumption on `w` or `v`. The proof needs this small change: use the derived nonnegativity of the majorants in place of `hw`/`hv`, either by re-proving `bilinear` without them or by inlining the argument.
- `(hv : ∀ n x, x ∈ s.domain → 0 ≤ v n x)` (theorem): The statement stays true without it, and it can be dropped together with `hw`. The proof of `LocalJets.bilinear`, which `local_mul` calls, uses `hv` only to show `0 ≤ majorant s v β B q n x` via `majorant_nonneg`. At `x ∈ s.domain ∩ K n i`, `hg.bounds` with `j = 0` gives `0 ≤ ‖g n i x‖ ≤ majorant s v β B q n x`, so the majorant is nonnegative without any assumption on `v`. The remaining steps (`bilinear_jet_at`, `majorant_mul`, nonnegativity of the constant) need no sign of `v`. The proof needs the same small change as for `hw`: take the majorant's nonnegativity from the `j = 0` bound instead of from `hv`.

### [`RS.kernelSubobject_tensorHom_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RegtsSevenster/RS/Classical/Deligne/KernelPow.lean#L729-L761) — `lean-pool-0091`

Snippet: `samples/lean-pool/lean-pool-0091.lean`

- `[Epi p₁]` (theorem): The statement is still true without `Epi p₁`, and `p₁` is not needed to be epi anywhere else in the statement. The hypothesis is used only to get `Epi (p₁ ▷ kernel p₂)` through `epi_whiskerRight_of_epi`, for the covering step `hv`. To remove it, factor `p₁ = e ≫ i`, where `e = factorThruImage p₁` is epi and `i = image.ι p₁` is mono.

In the rigid category `A`, `tensorRight W` and `tensorLeft W` preserve all limits. The library already shows this for kernels in `exists_kernel_ι_whiskerRight` and `exists_kernel_ι_whiskerLeft` (the `PreservesLimitsOfSize` instances). So `i ▷ W₂` is mono.

Write `p₁ ⊗ₘ p₂ = (e ⊗ₘ p₂) ≫ (i ▷ W₂)`, using `tensorHom_def` and the interchange of `i` with `p₂`. Then `kernelSubobject (p₁ ⊗ₘ p₂) = kernelSubobject (e ⊗ₘ p₂)`, because the second factor is mono (`kernelSubobject_comp_mono` in Mathlib). Apply the existing proof to `e`, which is epi, to get a bound by `imageSubobject (kernel.ι e ▷ Z₂) ⊔ imageSubobject (Z₁ ◁ kernel.ι p₂)`. Since `kernel e` and `kernel p₁` are the same subobject of `Z₁`, the first image equals `imageSubobject (kernel.ι p₁ ▷ Z₂)`.

I checked the degenerate cases: `p₁ = 0`, `p₁` mono but not epi, and `Z₁ = 0`. The inclusion holds in each. The proof changes but the conclusion is unchanged.

### [`Egrs75.ClearingP3.lowDigits_half_pred_pow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Egrs75/SubtractBranch.lean#L172-L181) — `lean-pool-0093`

Snippet: `samples/lean-pool/lean-pool-0093.lean`

- `(hp : 3 ≤ p)` (theorem): Odd p already gives p ≥ 1 and p ≠ 2, so the only case hp excludes is p = 1. In that case the statement still holds: (1^m - 1)/2 = 0, and LowDigits 1 0 is `∀ d ∈ Nat.digits 1 0, d ≤ 0`. Nat.digits 1 0 = [], so it holds. It is also the lemma RoundUp.lowDigits_zero 1. Proof: do `by_cases p = 1`. If p = 1, subst, simp turns the argument into 0, and use RoundUp.lowDigits_zero 1. Otherwise p ≥ 3 follows from Odd p (p ≠ 0, p ≠ 2, by omega with the witness from Odd), and the existing induction proof goes through.

### [`NFChoice.Compiler.NFCompactLeafFinalGate.axSiCompact`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NFWeakPartition/NFCompactLeafFinalGate.lean#L209-L255) — `lean-pool-0096`

Snippet: `samples/lean-pool/lean-pool-0096.lean`

- `(hzw : z ≠ w)` (theorem): The statement stays true when z = w. In that case the inner `.all w` shadows `.all z`. After `intro v`, `Wff.holds_ex`, and `intro Z W`, the valuation is v' = update (update (update v y Y) z Z) w W. With z = w, v' z = v' w = W. The goal then reads ({W},{W}) ∈ Y ↔ (W,W) ∈ v x. That is exactly `hY W W` from the same axSi instance (`formulaHolds_ex.mp (hLit (v x))` gives Y with ∀ Z W, ...), so `hY` already applies at the pair (W,W).

The proof only needs a case split. If z ≠ w, run the existing proof. If z = w, `subst`, and take xs := cons W (cons W (cons Y (cons (v x) nil))) and hiff := formulaHolds_biimp.mp (hY W W). Then hz : v' z = lookup xs 1 holds because both sides are W, via `update_same`. hw is unchanged. hy and hx still follow from hyz, hyw, hxz, hxw and hxy. The same `holds_literalSingletonPairMem` and `holds_literalPairMem` calc then goes through, since those lemmas only need the three `v _ = lookup xs _` equations and no distinctness. hzw is used in the proof only to rewrite the `update` terms for hz, hy and hx, and the z = w case replaces that with the direct computation above.

I checked only hzw. The other distinctness hypotheses change which variable is bound or free, so I did not claim any of them is removable.

### [`NavierStokes.TerminalCompensation.physicalProfile_family_contDiffOn`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TerminalCompensation.lean#L1082-L1099) — `lean-pool-0105`

Snippet: `samples/lean-pool/lean-pool-0105.lean`

- `(hR : 0 < R)` (theorem): The statement is still true for every real R. The profile is `a * (baseProfile lam (X/R) + correction P c (X/R))` with `baseProfile lam x = x ^ (slope lam)` (real rpow). On `U ×ˢ Ioi 0` we have z.2 > 0.

- If R ≠ 0, then z.2/R ≠ 0. `Real.contDiffAt_rpow_const_of_ne` only needs `z.2/R ≠ 0`, which follows from `div_ne_zero hz.2.ne' hR0`. So the positivity proof `div_pos hz.2 hR` can be replaced by this.
- If R = 0, then `z.2/0 = 0` by the junk-value convention. So `baseProfile lam (z.2/R)` is the constant `0 ^ slope lam`, which is smooth. The correction term is `correction P (c z.1) 0`, which is smooth by `correction_family_contDiffOn` composed with the smooth map z ↦ (z.1, 0) (the proof's `contDiffOn_snd.div_const R` already gives this).

The `hr` step and the final `mul`/`add` step do not use `hR`. Only `hb` does, so the proof needs a case split on R = 0 and nothing else.

### [`NavierStokes.PolarCharts.chart_finiteJets_uniform`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalGraphBounds.lean#L336-L354) — `lean-pool-0108`

Snippet: `samples/lean-pool/lean-pool-0108.lean`

- `{a : ℝ} (ha : 0 < a)` (theorem): The only use of `ha` is `chart_contDiff ha i.1`, to get `ContDiff ℝ ∞ (chart a j)`. That smoothness holds for every real `a`, so the theorem stays true without `ha`. I checked this against `chart`, `extendedBase` and `RadialPullback.positiveRadius` (`positiveRadius ℓ x = ℓ + (x-ℓ) * smoothTransition ((x-ℓ)/ℓ)`). `positiveRadius_contDiff ℓ` has no positivity hypothesis. `extendedBase a` is `(√(positiveRadius (a²/32) (p.1²+p.2²)), arctan (p.2 / positiveRadius (a/8) p.1))`, and `chart a j` is a smooth composition of it with `rotate j`, plus a constant. The only places `ha` was used are the nonvanishing of the two `positiveRadius` terms (for `sqrt` and the division). The remaining cases are:
- Case a > 0: this is the original proof.
- Case a < 0: `a²/32 > 0`, so the first `positiveRadius` is positive by `positiveRadius_pos`. For the second, ℓ = a/8 < 0. Write t = (x-ℓ)/ℓ. Then `positiveRadius ℓ x = ℓ(1 + t·smoothTransition t)`, and `t·smoothTransition t ≥ 0` for all t, because `smoothTransition` is 0 for t ≤ 0 and nonnegative otherwise. So the bracket is ≥ 1 and the value is nonzero for every x. The division is therefore smooth.
- Case a = 0: `positiveRadius 0 x = x * smoothTransition 0 = 0`, using `x/0 = 0` and `smoothTransition 0 = 0`. So `extendedBase 0` is the constant `(√0, arctan 0)`, and `chart 0 j` is the constant `(0, offset j)`. Both are smooth.

So `∀ a, ContDiff ℝ ∞ (chart a j)`. The rest of the proof is unchanged: compactness of `closedBall`, continuity of `iteratedFDeriv`, the finite sum of bounds over `Index × Fin (m+1)`, and the choice of `C = 1 + ∑ |B i|`. The conclusion does not mention `ha` at all. The proof would need a small separate lemma `∀ a, ContDiff ℝ ∞ (chart a j)`, proved by the case split above, in place of `chart_contDiff ha`.

### [`NavierStokes.SlowStressSupport.axial_stress_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/SlowStressSupport.lean#L2093-L2133) — `lean-pool-0111`

Snippet: `samples/lean-pool/lean-pool-0111.lean`

- `(hn : 0 < n)` (theorem): The proof uses hn only once, to prove `hprev_le : n - 1 ≤ n` via `Nat.sub_lt hn ...`. That inequality holds for every n (natural subtraction), and the proof already proves the same fact elsewhere with `Nat.sub_le _ _`. So `have hprev_le : n - 1 ≤ n := Nat.sub_le n 1` replaces it. No other lemma called in the proof takes hn, and n does not appear in the statement in a way that needs positivity. For n = 0, `n - 1 = 0` and the statement still typechecks, and the argument goes through unchanged. Deleting hn is therefore fine.

### [`CKN.Leray.mildShiftedStokesIntegral_continuous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierMildIntegral.lean#L216-L225) — `lean-pool-0117`

Snippet: `samples/lean-pool/lean-pool-0117.lean`

- `(hC : 0 ≤ C)` (theorem): hC follows from hFC. Since ℝ is nonempty, 0 ≤ ‖F 0‖ ≤ C, which is `(norm_nonneg _).trans (hFC 0)`. In the proof, hC is only passed to the inner lemma, and there it is only used to get `0 ≤ B`. Replace it with this derived fact. Deleting hC leaves the statement true and provable.
- `(hT : 0 ≤ T)` (theorem): The statement stays true for T < 0. In that case `Set.uIoc 0 T = Ioc T 0`, so every τ in it has τ ≤ 0. The integrand `mildShiftedStokesIntegrand F t τ` is 0 whenever ¬(0 < τ), so the interval integral is 0 for every t. The function is then constant and continuous. A proof splits on `0 ≤ T`. The case `0 ≤ T` is the existing proof. The case T < 0 uses `intervalIntegral.integral_congr` to rewrite the integrand to 0 on `uIoc`, and then `integral_zero` gives a constant function. In the existing proof, hT is used only for `Set.uIoc_of_le hT`. Only the dominated-convergence bound needs hT, because `τ^(-1/2)` can be negative for τ < 0. This hypothesis can be deleted on its own, independently of hC.

### [`ESS.buGaussian_shifted_trace_strip_tendsto`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Linear/BUGaussianAverageTools.lean#L334-L436) — `lean-pool-0118`

Snippet: `samples/lean-pool/lean-pool-0118.lean`

- `(hB : MeasurableSet B)` (theorem): hB is used only as `hB.prod measurableSet_Ioc` to supply the measurability argument of `setIntegral_congr_ae` in two places (hleft and hright). In both places the integrands are equal at every point, not only on the set. In hleft, the proof's `hqmem` is never used; the step `buGaussian_timeShift_point_symm_apply σ q` holds for all q. In hright, `simp [F]` proves the equality pointwise. So the set-integral congruence can be replaced by `congr 1; funext q; ...` or `integral_congr_ae (Filter.Eventually.of_forall ...)`, and that needs no measurability of the set. The change-of-variables step `MeasurePreserving.setIntegral_image_emb` with `τprod.measurableEmbedding` holds for arbitrary sets. `setIntegral_parabolic_to_product` has no measurability hypothesis (its implicit arguments are only Ω, I, F). `himage` is purely set-theoretic. The remaining steps are unchanged. The statement is therefore still true and provable for arbitrary B.

### [`PDL.localInterpolantStep_oneSidedR`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/Local.lean#L307-L366) — `lean-pool-0128`

Snippet: `samples/lean-pool/lean-pool-0128.lean`

- `(def_rule : rule = LocalRule.oneSidedR orule YS_def)` (theorem): The statement never mentions def_rule. The LocalRuleApp in the conclusion is built with `lr := LocalRule.oneSidedR orule YS_def` and `hC := hC`, where hC is about `rule`. That already typechecks without def_rule, because `applyLocalRule` (Rules.lean:326) ignores its rule argument (`| _, ⟨L,R,O⟩ => ress.image ...`) and only uses the indices Lcond, Rcond, Ocond and ress. So `applyLocalRule rule (L,R,o)` and `applyLocalRule (oneSidedR orule YS_def) (L,R,o)` are definitionally equal. The only use of def_rule in the proof is `c_in' : (L',R',o') ∈ C := hC ▸ def_rule ▸ c_in`. Here c_in comes from `oneSidedR_sat_down` and has type `∈ applyLocalRule (LocalRule.oneSidedR orule YS_def) ⟨L,R,o⟩`. Without def_rule, `by rw [hC]; exact c_in` (or `hC ▸ c_in`) closes the goal, since `exact` unifies up to the same definitional equality. The theorem therefore stays true and provable with def_rule deleted, and the rest of the statement is unchanged. `rule` itself must stay because hC mentions it.

### [`GerverSofa.PartC.Stage2.rhoC_nonneg`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MovingSofa/GerverSofa/KernelOnly/Core/Bundle006.lean#L896-L906) — `lean-pool-0129`

Snippet: `samples/lean-pool/lean-pool-0129.lean`

- `(ht : t ∈ Set.Icc (0 : ℝ) T)` (theorem): The statement stays true for every real t. rhoC is a piecewise definition. If t ≤ params.phi, the value is 1/2. If params.phi < t ≤ params.theta, the value is t/2 - b1. If theta < t ≤ eta, the value is 1 + c2 + t. If eta < t ≤ tau, the value is a quadratic. If t > tau, the value is 0. The proof uses ht only through ht.1 (0 ≤ t), in the phase 2 and phase 3 branches. In those branches 0 ≤ t follows from the case hypotheses instead. The file already has `phi_nonneg : 0 ≤ params.phi` (line 662). In the phase 2 branch, hφ : ¬ t ≤ params.phi gives params.phi < t, so 0 ≤ t. In the phase 3 branch, theta < t and phi ≤ theta (`switchOrder.phi_le_theta`), so 0 ≤ t; `theta_lower_crude` (2/3 ≤ theta) also works. The phase 4 lemma `rhoC_phase4_nonneg` does not use ht at all. It derives 0 ≤ t from eta ≤ t and `four_fifths_lt_eta`. The first and last branches are `norm_num`. The upper bound t ≤ T is never used. So the proof becomes `rhoC_phase2_nonneg (le_of_lt (lt_of_le_of_lt phi_nonneg (not_le.mp hφ)))`, and similarly for phase 3, and the theorem holds for all t.

### [`AVenhance.Infra.Section5.Contracts.sds_gradMatrix_entry_periodic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/Contracts/TermCenteredAnalyticSmooth.lean#L49-L57) — `lean-pool-0130`

Snippet: `samples/lean-pool/lean-pool-0130.lean`

- `(hF : Differentiable ℝ F)` (theorem): The conclusion only involves gradMatrix F x i j = spaceGrad (fun y => F y j) x i = fderiv ℝ (fun y => F y j) x (basisVec i). Write G y = F y j. From `he`, G (y + latticeShift k) = G y + (k j : ℝ) for every y. Mathlib has `fderiv_comp_add_right (a) : fderiv 𝕜 (fun x ↦ f (x + a)) x = fderiv 𝕜 f (x + a)` and `fderiv_add_const (c) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x`. Neither needs differentiability. So fderiv ℝ G (x + latticeShift k) = fderiv ℝ (fun y => G (y + latticeShift k)) x = fderiv ℝ (fun y => G y + k j) x = fderiv ℝ G x. This holds in every case, including points where G is not differentiable, where both fderivs are the junk value 0. Rewrite the proof as: `intro k x; change fderiv ℝ (fun y => F y j) (x + latticeShift k) (basisVec i) = fderiv ℝ (fun y => F y j) x (basisVec i)`, then rewrite with `← fderiv_comp_add_right`, replace the function using `he` (the j-th component of `he k y`, via funext), and finish with `fderiv_add_const`. The hypothesis `he` is still needed. Nothing else in the statement mentions `hF`.

### [`RS.LaurentTail.injG_apply_of_not_mem`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/LaurentTail/Comparison.lean#L1239-L1247) — `lean-pool-0131`

Snippet: `samples/lean-pool/lean-pool-0131.lean`

- `[T1Space X]` (variable): The theorem also takes `[T2Space X]` from the same `variable` line, and `[T2Space X]` is needed because `injG` takes it. Mathlib has `instance (priority := 100) T2Space.t1Space [T2Space X] : T1Space X` (Mathlib/Topology/Separation/Hausdorff.lean:115). So `[T1Space X]` is implied by the other hypotheses. The only place the statement uses T1Space is as an instance argument of `injG`, through `compOpens` in `injPatch`/`cleanNbhd`. Without the binder, that argument is filled in by `T2Space.t1Space`, so the statement elaborates and means the same thing. The proof is unchanged. It only unfolds `injG` as a `dite` and uses `dite_eq_right`, so it never touches the T1 instance. Deleting the argument, for example with `omit [T1Space X] in`, is therefore harmless. The other instances are needed: `injG` or `cleanNbhd` uses `CompactSpace` (`isCompact_univ`), `DecidableEq` (`Finset.erase`) and `IsManifold`. I did not check whether `T2Space` is also removable, and it can't be removed together with `T1Space`.

### [`polytopeRoundedSupportCurve_regular`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/OperatorTheory/Operator/Crouzeix/SmoothSupportCurve.lean#L231-L242) — `lean-pool-0133`

Snippet: `samples/lean-pool/lean-pool-0133.lean`

- `(hu : u.Nonempty)` (theorem): The statement is still true for u = ∅. There polytopeSoftPartition ∅ delta theta is an empty sum, so it equals 0. Then polytopeSoftSupport ∅ delta theta = delta * Real.log 0 = 0, using Real.log 0 = 0. So polytopeRoundedSupport ∅ delta rho is the constant function rho. Its first and second derivatives are 0. smoothSupportCurve h theta = h theta • n + deriv h theta • (n*I), where n = circleMap 0 1 theta. This reduces to rho • n, and its derivative is rho • (n*I). That is nonzero because rho > 0 and ‖n‖ = 1. Equivalently, smoothSupportCurvatureRadius = rho + 0 > 0, so smoothSupportCurve_regular applies, and it needs only ContDiff ℝ ∞ h and positivity of the radius. The proof changes only by a case split. If u.Nonempty, use the existing proof. Otherwise use Finset.not_nonempty_iff_eq_empty to get u = ∅, then simp [polytopeRoundedSupport, polytopeSoftSupport, polytopeSoftPartition] shows the support function is const rho. Then contDiff_const gives smoothness, and deriv_const (twice) gives the radius rho > 0. hu is used only through contDiff_polytopeRoundedSupport and polytopeRoundedSupport_add_deriv_deriv_pos, and both need it only to keep Real.log away from 0. The statement itself does not mention hu beyond u. hdelta and hrho are not claimed removable.

### [`QuadraticCarleson.packetPoint_abs_sub_right_ge`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/CounterexampleGeometry.lean#L68-L86) — `lean-pool-0135`

Snippet: `samples/lean-pool/lean-pool-0135.lean`

- `(hN : 100 ≤ N)` (theorem): hN is used only to get (k.toNat : ℝ) = k via paperBohrIndex_cast_toNat, which needs k ≥ 0. That already follows from hk alone. By mem_paperBohrIndices, hk gives 3*(N:ℝ)/5 ≤ k, and (N:ℝ) ≥ 0 because N : ℕ, so (0:ℝ) ≤ k and therefore 0 ≤ k in ℤ. This holds for every N, including N = 0, where the index set is {0}. Then Int.toNat_of_nonneg (the lemma the existing helper already uses) gives (k.toNat : ℤ) = k, and exact_mod_cast turns that into the real-cast statement. The rest of the proof (abs_of_nonpos, Nat.cast_sub hj, linarith with hτ.2) never mentions N. So the theorem stays true and provable with hN deleted. Only the helper step changes, to a short argument: have h0 : (0:ℝ) ≤ k := by have := (mem_paperBohrIndices.mp hk).1; positivity-style linarith with Nat.cast_nonneg N, then exact_mod_cast Int.toNat_of_nonneg (by exact_mod_cast h0).

### [`NavierStokes.PhysicalCoordinateBounds.xLift_homogeneous`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/PhysicalCoordinateBounds.lean#L421-L426) — `lean-pool-0136`

Snippet: `samples/lean-pool/lean-pool-0136.lean`

- `{y : Point} (_hy : y ∈ positiveTime)` (theorem): The proof never uses `_hy`; only `hr` is used. `xLift y = y.2.1 / y.1`, and `dilation a r y = (r*y.1, (r*y.2.1, r^D a * y.2.2))`, so `xLift (dilation a r y) = (r*y.2.1)/(r*y.1)`. This equals `y.2.1 / y.1` for any `y`, because `r ≠ 0` (from `hr`). That holds even when `y.1 = 0`, where both sides are junk-value 0 (`mul_div_mul_left` needs only `r ≠ 0`). The right side is `r^0 * xLift y = xLift y`. After deleting `_hy`, the statement keeps `y : Point` as an ordinary argument and the same proof compiles unchanged. (Only the membership hypothesis `_hy` is deleted; `y` stays.)

### [`NavierStokes.TemporalMeanUpdate.meanClass_axialAlias`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TemporalMeanUpdate.lean#L1535-L1567) — `lean-pool-0159`

Snippet: `samples/lean-pool/lean-pool-0159.lean`

- `(hM : ∀ n, M n ≠ 0)` (theorem): hM is not needed for the statement to hold. Its only use is in the chain meanClass_dividedAlias → dividedAlias_global_bounds, where it is passed to UniformFourierAlias.real_exactAlias_finiteJets (that lemma has `M ≠ 0` as a hypothesis). It is used nowhere else in the proof. The other ingredients (physicalAlias_contDiff, physicalAlias_supported, dividedAlias_interior_support, dividedAlias_finiteJets_transfer, and the desiredIncrement lemmas) take arbitrary M n, and the statement never mentions hM or M n ≠ 0.

The case M n = 0 is still true. There `TransportPrimitive.shift 0 v z u = z + (u, 0)`, so `exactAlias χ 0 v G z = deriv χ z.1 • ∫ u, G (z.1+u, z.2)`. This is the product of a smooth function of z.1 and the function H(z.2) = ∫ G(r, z.2) dr. G is smooth and radially supported in [a^d, b^d], so H is an integral over a compact interval and is not junk. The jets of H of order ≤ m are bounded by (b^d - a^d)·B, where B bounds the jets of G on the strip. The input `FiniteJetBound (m + 6*0) G` is exactly what hsource provides. By Leibniz, the jets of the product are bounded by K·B, with K depending only on χ, m, a, b. This is the same bound form KA*B that the proof already uses (the exponent p is 0 there, so the bound is uniform in M and has no |M|⁻¹ blow-up). The rest of the proof, via dividedAlias_finiteJets_transfer, carries over unchanged.

So `hbA` can be proved for M = 0 by this direct argument, with a short case split `M n = 0` versus `M n ≠ 0` inside dividedAlias_global_bounds. The same deletion works for the intermediate lemma meanClass_dividedAlias, so the final theorem can drop hM.

### [`PDL.LoadedCluster.satDown_three_not_basic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PDL/Interpolation/ClusterSatDown.lean#L575-L602) — `lean-pool-0171`

Snippet: `samples/lean-pool/lean-pool-0171.lean`

- `(hlen : next.length = (C.stepOfL Δ).length)` (theorem): hlen is used only in `have hi' : i < next.length := by omega`, where i < (C.stepOfL Δ).length comes from `hS.nonBasicStep`. The same fact follows from the other hypotheses. Since `hi : i < (C.stepOfL Δ).length`, `hlab i hi` gives `C.Q.labelAt (x ++ [i]) = some _`. `labelAt q y` is `(q.atOpt y).map label` (QuasiTableau.lean:298), so `C.Q.atOpt (x ++ [i])` is `some _`. By `QuasiTab.atOpt_snoc` (PreInterpolant.lean:202), `atOpt (x ++ [i]) = (atOpt x).bind (fun n => n.children[i]?)`. With `hx` and `QuasiTab.children (QNode _ _ next) = next`, this is `next[i]?`. That is `some _` only if `i < next.length`. A proof: `by_contra hge; have hl := hlab i hi; unfold QuasiTab.labelAt at hl; rw [QuasiTab.atOpt_snoc, hx] at hl; simp [QuasiTab.children, List.getElem?_eq_none (by omega : next.length ≤ i)] at hl`. Nothing else in the statement mentions hlen. The theorem therefore stays true and provable without it, with the rest of the proof unchanged.

### [`NavierStokesAndEuler.SmoothCutoff.cutoff_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/ForMathlib/SmoothCutoff.lean#L86-L90) — `lean-pool-0181`

Snippet: `samples/lean-pool/lean-pool-0181.lean`

- `(hR : 0 < R)` (theorem): hR can be dropped. From hx : ‖x‖ ≤ R we get 0 ≤ ‖x‖ ≤ R, so R ≥ 0. If R > 0, the existing proof works. If R = 0, then ‖x‖ ≤ 0 gives x = 0. Then cutoff E 0 0 = baseCutoff E (0⁻¹ • 0) = baseCutoff E 0 = 1 by baseCutoff_eq_one, since ‖0‖ ≤ 1. (In fact R⁻¹ • x = 0 • x = 0 anyway, since R⁻¹ = 0.) R < 0 is impossible because ‖x‖ ≥ 0. So the statement stays true. A proof: rcases (norm_nonneg x).trans hx |>.eq_or_lt, using the old argument for R > 0 and, for R = 0, `simp` after getting x = 0 via norm_le_zero_iff, then baseCutoff_eq_one with norm_zero. The statement does not mention hR elsewhere, so it can be deleted on its own.

### [`BooleanIsoperimetry.harper_macaulay_min`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanIsoperimetry/MacaulayMin.lean#L154-L176) — `lean-pool-0191`

Snippet: `samples/lean-pool/lean-pool-0191.lean`

- `(ha : a ≤ 2 ^ N)` (theorem): The statement stays true without `ha`. `H n k` is the size of the radius-1 neighborhood of `simplicialInitSeg n k = univ.filter (rank x < k)`, and `rank_lt_two_pow` gives `rank x < 2^n`. So for `k ≥ 2^n` the initial segment is the whole cube, and `H n k = 2^n`. Suppose `a > 2^N`. Then `H N a = 2^N` (the neighborhood contains the initial segment, and `H_le_cube` gives the upper bound), so `max (H N a) b ≥ 2^N` and `max (H N b) a ≥ a > 2^N`. The RHS is therefore `> 2^(N+1)`, while the LHS is `≤ 2^(N+1)` by `H_le_cube`. If `a ≤ 2^N`, the original proof applies, using `hb` if it is kept (or the symmetric argument if `b > 2^N`). The hypothesis can be dropped together with `hb`. The proof becomes a case split on `a ≤ 2^N` and `b ≤ 2^N`: the existing argument handles the case where both hold, and `H_le_cube` with the bound above handles the rest.
- `(hb : b ≤ 2 ^ N)` (theorem): This is symmetric to `ha`. If `b > 2^N`, then `H N b = 2^N`, so `max (H N b) a ≥ 2^N` and `max (H N a) b ≥ b > 2^N`. The RHS is `> 2^(N+1) ≥ H (N+1) (a+b)` by `H_le_cube`. The case `b ≤ 2^N` is handled by the existing proof. Both `ha` and `hb` can be deleted together, because whenever either bound fails the inequality holds by the size bound above, regardless of the other variable.

### [`PebblingLean.Hypercube.PaperParameters.normalizedCost_recursiveCostBound_step_of_ceiling`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PebblingLean/UpperBoundParameters.lean#L2099-L2138) — `lean-pool-0205`

Snippet: `samples/lean-pool/lean-pool-0205.lean`

- `(hsmall : splitM K n < n)` (theorem): hsmall is implied by hslack. Suppose splitM K n ≥ n. Then splitA K n = n - splitM K n = 0, so hslack reads 1 ≤ loss n * (4/3)^0 = (n^2)⁻¹. For n = 0, loss 0 = 0, so 1 ≤ 0 is false. For n ≥ 2, (n^2)⁻¹ ≤ 1/4 < 1, so it is false. For n = 1, Real.log 1 = 0 gives splitM K 1 = ⌈K * √(1*0)⌉₊ = ⌈0⌉₊ = 0 < 1, which contradicts splitM K n ≥ n directly. So in every case splitM K n < n holds. The proof can begin with `have hsmall : splitM K n < n := by by_contra h; ...`, doing a case split on n and using Real.log_one. The rest of the proof is unchanged, and recursiveCostBound_step hn hsmall still applies. The other two hypotheses are needed: hslack because K=0, n0=0, n=2 gives 27/16 > 1.5 as a counterexample, and hn because K=0, n=25, n0=26 gives a counterexample.

### [`AleksandrovDifferentiability.prod_measure_diff_eq_zero_of_forall_ae_restrict_section₀`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/AleksandrovDifferentiability/Analysis/GoodSet.lean#L97-L106) — `lean-pool-0218`

Snippet: `samples/lean-pool/lean-pool-0218.lean`

- `[SFinite ν]` (theorem): The statement does not need s-finiteness to elaborate: `μ.prod ν` is defined for any `ν` (it takes the junk value 0 if `ν` is not s-finite, see Measure.prod in Mathlib/MeasureTheory/Measure/Prod.lean). The proof uses it only through `Measure.measure_prod_null htmeas`, and only in the direction `(fun x => ν (Prod.mk x ⁻¹' t)) =ᵐ[μ] 0 → μ.prod ν t = 0`. Mathlib has `Measure.measure_prod_null_of_ae_null` (hsm : MeasurableSet s) (hs : (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0) : μ.prod ν s = 0, which is stated `omit [SFinite ν]` and relies on `prod_apply_le`, which also needs no s-finiteness. So the proof of the theorem goes through without the hypothesis. First take the measurable `t ⊆ s \ G` that is a.e.-equal to `s \ G`, as in the existing proof. Then, for each `x`, show `ν (Prod.mk x ⁻¹' t) = 0` by the same section argument, which uses no s-finiteness. Conclude `μ.prod ν t = 0` with `measure_prod_null_of_ae_null htmeas` applied to `Filter.Eventually.of_forall` of that fact, and finish with `measure_congr`. The other hypotheses (`hs`, `hbad`, `hsection`) are still used. The only dependence on `[SFinite ν]` is in the helper `prod_measure_diff_eq_zero_of_ae_ae_restrict_section₀`, which would have to be reproved or generalized in the same way.

### [`TauCeti.DavisKahan.ExactSinTheta.generalizedSinTheta_unbounded_real_reducingSubspace`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/SinTheta/Natural/Reducing.lean#L496-L543) — `lean-pool-0223`

Snippet: `samples/lean-pool/lean-pool-0223.lean`

- `(hAdense : Dense (A.domain : Set ER))` (theorem): Implied by hA. Mathlib has `IsSelfAdjoint.dense_domain` (Mathlib/Analysis/InnerProductSpace/LinearPMap.lean): a self-adjoint LinearPMap has dense domain, because the adjoint is junk for non-dense domains. The proof only uses density in building the record field `A_dense` and in `reducingRestriction_isSelfAdjoint` (the library's own wrapper already passes `hA.dense_domain`). So replace `hAdense` with `hA.dense_domain`.
- `(hAclosed : A.IsClosed)` (theorem): Implied by hA. Mathlib has `IsSelfAdjoint.isClosed` (same file), so `hA.isClosed` supplies the record field `A_closed`. The engine `generalizedSinTheta_unbounded_exact_real` and `unboundedSinThetaDataOfReducingSubspace` never use closedness (their closedness arguments are underscore-named).
- `(hA0dense : Dense (A0.domain : Set FR))` (theorem): Implied by hA0 via `IsSelfAdjoint.dense_domain`. It is only used to fill the record field `A₀_dense`, which `toData` ignores, so replace it with `hA0.dense_domain`.
- `(hA0closed : A0.IsClosed)` (theorem): Implied by hA0 via `IsSelfAdjoint.isClosed`. It is only used to fill the record field `A₀_closed`, which `toData` ignores (the argument is `_hA0closed`), so replace it with `hA0.isClosed`. Each of the four hypotheses can be deleted on its own, and all four can be deleted together.

### [`BGS.CorvajaZannier.exists_support_direction_of_not_rankTwo`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveSupportRank.lean#L186-L216) — `lean-pool-0224`

Snippet: `samples/lean-pool/lean-pool-0224.lean`

- `(hnonsingleton : ∃ s ∈ f.support, s ≠ r)` (theorem): It is only used to get a second support point s so that planeExponentDifference r s ≠ 0 and a primitive direction v can be extracted. Without it, split on whether such an s exists. If it does, the existing proof applies unchanged. If not, then since r ∈ f.support, every s ∈ f.support equals r. Take v = Pi.single 0 1, which is nonzero. For s = r, planeExponentDifference r r = fun i => (r i:ℤ) - (r i:ℤ) = 0 = (0:ℤ) • v, so k = 0 works. The conclusion is therefore still true without the hypothesis, and the degenerate case is the singleton support {r}. The other hypotheses, hr and hnrank, stay in place.

### [`CarlsonFunctions.SeveralComplexVariables.norm_sub_le_of_separately_analytic_bounded`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CarlsonFunctions/SeveralComplexVariables/LocallyBounded.lean#L67-L108) — `lean-pool-0237`

Snippet: `samples/lean-pool/lean-pool-0237.lean`

- `(hr : 0 < r)` (theorem): hr is not needed for the statement to be true. The hypothesis hx : x ∈ closedBall c r gives dist x c ≤ r, so r ≥ 0. (If r < 0 the ball is empty and hx is absurd.) If r = 0, then closedBall c 0 = {c}, so x = c = y. Then f y - f x = 0 and ‖y - x‖ = 0, so the right side is card ι * (M/0) * 0 = 0 and the inequality is 0 ≤ 0. This holds despite the junk value M/0 = 0. If r > 0, the existing proof applies unchanged. So the proof can start by deriving 0 ≤ r from hx. It then splits on r = 0 (use closedBall_zero or dist_le_zero to get x = y = c, then simp) and r > 0 (obtain hr and run the current proof). The statement of the theorem does not otherwise mention hr, so it can be deleted without changing the statement.

### [`EulerPacketTerminalDatum.forwardInitializedPacket_normalized_bound`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/PacketForwardInitializedCorrectionData.lean#L76-L84) — `lean-pool-0242`

Snippet: `samples/lean-pool/lean-pool-0242.lean`

- `(hα : 0 < α)` (variable): hα is derivable from hgrowth. S.growth_pos gives 0 < S.growth t for all t. timeProfileChange_pos (PacketBudgetTimeChange.lean:29) then gives 0 < timeProfileChange S.growth hTime t' for every t' in Icc 0 D.T. Take t' = ⟨0, le_rfl, D.T_pos.le⟩. hgrowth gives timeProfileChange S.growth hTime t' = α * L.g t', and L.positive gives 0 < L.g t'. Hence α > 0, for example by contradiction with nlinarith. The statement and conclusion never mention hα: forwardInitializedPacketField takes only α. So the theorem is unchanged without it. The proof first builds a local `have hα : 0 < α` this way, then passes it to forwardPacket_normalized_bound and forwardInitialized_primary_budget as before.

### [`LeanPool.Besicovitch.sigma_mul_radius_div_two_le_diam_localAttachmentComponent`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Besicovitch/Rectifiability/ComponentDiameter.lean#L38-L191) — `lean-pool-0244`

Snippet: `samples/lean-pool/lean-pool-0244.lean`

- `(hsigma_one : sigma < 1)` (theorem): In the proof, `hsigma_one` is used only in `nlinarith` to get `hR_rho : sigma * rho / 2 < rho`. The hypothesis `hannulus` already gives this. It provides `w ∈ Metric.ball z rho` with `w ∉ Metric.ball z (sigma * rho / 2)`. So `sigma * rho / 2 ≤ dist w z < rho`. In the proof, take `obtain ⟨w, ⟨hw_outer, hw_inner⟩, hwF⟩ := hannulus` before `hR_rho`. Then prove `hR_rho` as `lt_of_le_of_lt (not_lt.mp (by simpa [Metric.mem_ball] using hw_inner)) (by simpa [Metric.mem_ball] using hw_outer)`, or with `Metric.mem_ball` and `not_lt`. No other step uses `sigma < 1`. `hR_nonneg` uses only `hsigma` and `hrho`. `uniformDensitySet_ball_measure_gt` is applied with `hsigma` and `hsigma_gamma` only. The statement is therefore still true and provable without `hsigma_one`. If `sigma ≥ 2`, `hannulus` is already contradictory, so the case is vacuous.

### [`CKN.norm_sub_integralAverage_le_volumeAverage_integral_norm_fderiv_mul_norm_sub_along_segment`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Sobolev/Poincare/Lp.lean#L159-L202) — `lean-pool-0254`

Snippet: `samples/lean-pool/lean-pool-0254.lean`

- `[MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]` (theorem): The statement never mentions this instance. `volumeMeasureOn U` is an abbrev for `volume.restrict U` (via `volumeOn`). The hypothesis `hvol : 0 < (volume U).toReal` already forces `volume U ≠ ⊤`, because `ENNReal.toReal ⊤ = 0`. Since `(volume.restrict U) univ = volume U`, the instance follows: `haveI : IsFiniteMeasure (volumeMeasureOn U) := ⟨by simpa [Measure.restrict_apply_univ] using lt_top_iff_ne_top.2 (ne_top_of_toReal_pos hvol)⟩`, with the exact lemma names to be looked up in Mathlib. The proof's other steps (constant integrable, the Mean lemma which takes this instance) then go through unchanged. This can be deleted together with `hu`, because the derivation of `hu` below uses the instance obtained from `hvol`.
- `(hu : MeasureTheory.IntegrableOn u U)` (theorem): `hu` follows from the other hypotheses. Let g y = ∫ t in 0..1, ‖fderiv ℝ u (segmentBlend x t y)‖ * ‖x - y‖. `hsegment` says g is integrable on U. The lemma `norm_sub_le_integral_norm_fderiv_mul_norm_sub_along_segment huDiff x y` (it needs only `ContDiff ℝ 1 u`) gives ‖u x - u y‖ ≤ g y for every y. The map y ↦ u x - u y is continuous because `huDiff.continuous` holds, so it is AEStronglyMeasurable. Hence `Integrable.mono'` gives IntegrableOn (fun y => u x - u y) U. The constant function u x is integrable on U because the restricted measure is finite (see the instance entry; it comes from `hvol`). So u = (fun _ => u x) - (fun y => u x - u y) is integrable on U. That recovers `hu`, which the proof only uses for `hsubInt` and for the call to `norm_sub_integralAverage_le_volumeAverage_integral_norm_sub`. The conclusion is unchanged, so the theorem remains true and provable without `hu`. `hvol` is genuinely needed: if volume U = 0 the right side is 0 but the left side is ‖u x‖.

### [`EGZ.CommonMeasure.final_mass_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ErdosGinzburgZiv/EGZ/Decomposition/CommonMeasure.lean#L109-L119) — `lean-pool-0276`

Snippet: `samples/lean-pool/lean-pool-0276.lean`

- `(hε : 0 < ε)` (theorem): Not needed, because hu is kept. If ε ≤ 0, then mass u P ≥ 0 (the sum of nonnegative terms, using hu), so ε/2 * mass u P ≤ 0. Also 0 ≤ mass u Q by hu. So the conclusion holds trivially. If ε > 0, the existing proof applies unchanged. The case split `rcases le_or_gt ε 0` makes it a short proof. This can be dropped on its own. It can also be dropped together with hR, using the same case analysis.
- `(hR : 0 < R)` (theorem): Not needed. Assume ε > 0, since ε ≤ 0 is trivial as above. The sum ∑(w a - u a) is nonnegative by hle, so hloss gives ε²/4 * R ≥ 0, hence R ≥ 0. If R > 0, use the existing proof. If R = 0, then hloss forces ∑(w-u) ≤ 0, so w = u pointwise. Then mass u P = mass w P ≤ R = 0, so ε/2 * mass u P ≤ 0 ≤ mass u Q by mass_nonneg, which holds because of hu. So the statement is true without hR, and the proof is a short case split on R. This can be dropped on its own.

### [`eigenvector_constant_sign`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SpectralPositivity/Operator/JentzschProof.lean#L332-L387) — `lean-pool-0280`

Snippet: `samples/lean-pool/lean-pool-0280.lean`

- `(hT_compact : IsCompactOperator T)` (theorem): Compactness is only used as an argument to `abs_eigenvector_of_top_eigenvector`, and that lemma never uses it (its binder is `_hT_compact`). Its proof uses only self-adjointness, via `hT_sa.eq_smul_self_of_isLocalExtrOn`, which needs no compactness. It also uses positivity preservation and the top-eigenvalue bound. The rest of `eigenvector_constant_sign` uses only `ground_state_strictly_positive`, which has no compactness hypothesis. So the theorem is still true and provable with `hT_compact` deleted. The only change is to drop the `_hT_compact` argument from `abs_eigenvector_of_top_eigenvector` and from the call (or pass a dummy). No degenerate cases are involved.

### [`QuadraticCarleson.annularQuadraticKernel_correlation_le_ordered`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/QuadraticFixedHeightAveragingCorrelation.lean#L49-L127) — `lean-pool-0281`

Snippet: `samples/lean-pool/lean-pool-0281.lean`

- `(hS : 0 < S)` (theorem): It follows from hR : 0 < R and hRS : R ≤ S, since `lt_of_lt_of_le hR hRS : 0 < S`. Add `have hS : 0 < S := lt_of_lt_of_le hR hRS` at the start of the proof and the rest is unchanged. The statement still elaborates, because S appears elsewhere in it.
- `(hH : 0 < H)` (theorem): It follows from hdecay : 1 ≤ H * u ^ 5 and hu : 0 < u. We have u^5 > 0 by `pow_pos hu 5`. If H ≤ 0 then H * u^5 ≤ 0 < 1, a contradiction. So `have hH : 0 < H := by by_contra h; push_neg at h; nlinarith [pow_pos hu 5]` or `pos_of_mul_pos_left` works. The proof only passes hH to the lemma, so it can be re-derived locally.
- `(hD : 0 ≤ D)` (theorem): It follows from hab : ∀ t, ‖a t‖ ≤ D / R and hR : 0 < R. At t = 0, 0 ≤ ‖a 0‖ ≤ D / R, so D / R ≥ 0 and therefore D ≥ 0 (`div_nonneg_iff` or `by_contra` with `div_neg_of_neg_of_pos`). hD is used only in the `by positivity` side goals (0 ≤ D / R ^ 2, 0 ≤ D / R, and so on). Derive it locally with `have hD : 0 ≤ D := ...` at the start of the proof. The other hypotheses stay unchanged. These three deletions are independent, so each can be removed on its own or all together.

### [`AVenhance.Infra.Section3.ChiMKCorrector.chiMK_spaceLap_three_active`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section3/ChiMKCorrector.lean#L159-L209) — `lean-pool-0282`

Snippet: `samples/lean-pool/lean-pool-0282.lean`

- `(hk : k % 4 = 3)` (theorem): The statement stays true without hk. By the definition of `uShear`, its component 0 is `-(2π a ε cos(2π x 1/ε))` only when k % 4 = 3. If k % 4 = 1 it is `![0, …] 0 = 0`, and in every other case the vector is `0`. So when k % 4 ≠ 3, `chiMK κ m k t y 0 = -(corrTime) * 0 = 0` for all y. Then the function `fun y => I.chiMK κ m k t y 0` is identically 0. Its `spaceLap` is 0, and the right side is `-(…) * 0 = 0`. The file already has `ChiMKCorrector.chiMK_spaceLap_of_zero_component`, which proves exactly this from `(fun y => I.chiMK κ m k t y j) = fun _ => 0`. A proof without hk does `by_cases hk : k % 4 = 3`. The positive case is the existing proof. The negative case shows the zero-component hypothesis by unfolding `Ingredients.chiMK` and `uShear` and splitting on k % 4 = 1 (component 0 of `![0, _]` is 0) or the else branch (the vector is 0), then applies `chiMK_spaceLap_of_zero_component`. No other hypothesis is touched.

### [`Malliavin.memLp_mderiv_cylinder_expGrowth`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Malliavin/Malliavin/CylindricalGrowth.lean#L488-L496) — `lean-pool-0295`

Snippet: `samples/lean-pool/lean-pool-0295.lean`

- `(hC : 0 ≤ C)` (theorem): It follows from hfg'. Take y = 0 in the type `Fin n → ℝ`, which is nonempty for every n. This gives 0 ≤ ‖fderiv ℝ f 0‖ ≤ C * exp (c * ‖0‖) = C * 1 = C. So `hC` can be rebuilt inside the proof with `have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hfg' 0)`. The rest of the proof (`expGrowth_coord_le hC hc L`) is unchanged. Deleting `hC` does not depend on deleting `hc`.
- `(hc : 0 ≤ c)` (theorem): The statement stays true for c < 0. Put c' = max c 0, so c' ≥ 0. Since C ≥ 0 (derived from hfg' as above) and exp is monotone, C * exp (c * ‖y‖) ≤ C * exp (c' * ‖y‖). So hfg' also holds with c' in place of c. Apply the same proof with c', i.e. `memLp_mderiv_cylinder_of_dominated` with ψ = C * exp (c' * ((∑ ‖L i‖) * ‖x‖)), `expGrowth_coord_le` (which needs 0 ≤ c') and `integrable_expGrowth_sq μ C c' _`. `integrable_expGrowth_sq` has no sign assumptions. The conclusion `MemLp (mderiv μ …) 2 μ` does not mention c, so it is unchanged. This deletion is independent of deleting `hC`.


## FLT (Anthropic) (54 flagged)

### [`P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.C2idemCore.IdempotentOrbit.exists_idempotent_orbit_or_isField`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField.lean#L172-L278) — `flt-anthropic-0014`

Snippet: `samples/flt-anthropic/flt-anthropic-0014.lean`

- `[Finite ι]` (theorem): The statement is still true without `[Finite ι]`, but only because the other hypotheses already force ι to be finite. The existing proof uses `Finite ι` only to get a `Fintype` for `kappa` and `exists_indexMap_of_iterate_eq`, so it would need a new argument for the infinite case.

Suppose ι is infinite, so it is nonempty. Then s is an automorphism, because s^n = id. For each j, the element s(ind{j}) is a nonzero idempotent of Π F_i. It is also minimal. If it were ind T with two points j1 ≠ j2 in T, then c = s⁻¹(ind{j1}) = s^(n-1)(ind{j1}) would be an idempotent with c·ind{j} = c, c ≠ 0 and c ≠ ind{j}. But an idempotent below ind{j} is either 0 or ind{j}, which is a contradiction. So s(ind{j}) = ind{ψ j} for a map ψ with ψ^n = id.

The ψ-orbit S of j has at most n elements, so it is a finite set. The element ind S is fixed by s. By `hfix` it equals f x for some x, and x is idempotent in the field k, so x = 0 or x = 1. Since ind S ≠ 0, we get ind S = 1, so S = univ and ι is finite. This contradicts the assumption that ι is infinite.

So with ι infinite the hypotheses `hn`, `hs`, `hfix` are inconsistent, and the conclusion holds vacuously. The empty case is already handled in the proof, because the empty type is finite.

The theorem is therefore true and provable without `[Finite ι]`. The statement still elaborates, because ι appears in `φ` and `F`, and `Finite ι` is not needed to state anything. The proof would first derive `Finite ι` (or work with finite orbits) as above, then run the existing proof.

### [`P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6.comp_heckeDiag_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.lean#L664-L678) — `flt-anthropic-0018`

Snippet: `samples/flt-anthropic/flt-anthropic-0018.lean`

- `(hp : p ≠ 0)` (theorem): The statement stays true without hp. `heckeDiagMatrix p` is defined as `if hp : p = 0 then 1 else upperTriangularGL p 0 1 _` (Definitions/Def_ModularForm_HeckeOperator.lean:21). For p = 0 it is the identity, so `fun τ => F (heckeDiagMatrix 0 • τ)` equals `fun τ => F (1 • τ)`, which is `F` and is nonzero by hF. For p ≠ 0 the existing proof applies unchanged. A proof without hp does `by_cases hp : p = 0`. In the zero case, `subst hp; intro h; apply hF; funext τ; simpa [ModularForm.heckeDiagMatrix] using congrFun h τ`. In the nonzero case it uses the current argument. Here hp is only used to apply `coe_heckeDiagMatrix_smul` and to cast p ≠ 0, and both uses sit inside the p ≠ 0 branch.

### [`P2MW.S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.Blk176Arith.not_cube_dvd_mul_prod_filter`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.lean#L147-L182) — `flt-anthropic-0038`

Snippet: `samples/flt-anthropic/flt-anthropic-0038.lean`

- `(hN0 : N ≠ 0)` (theorem): hN0 follows from hN3. If N = 0, then hN3 2 Nat.prime_two says ¬ 2^3 ∣ 0, which is false because everything divides 0. So hN3 already gives N ≠ 0. Deleting hN0 leaves the statement true. In the proof, start with `have hN0 : N ≠ 0 := by rintro rfl; exact hN3 2 Nat.prime_two (dvd_zero _)`, and the rest of the proof is unchanged. hS and hq are needed: for example S = {8}, N = 1 and q = 2 breaks the statement without hS, and q = 1 breaks it without hq.

### [`P2MW.S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.P2mS17LB.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_level_frobenius_pow_dvd_and_apply_eq.lean#L49-L111) — `flt-anthropic-0046`

Snippet: `samples/flt-anthropic/flt-anthropic-0046.lean`

- `(hn : 0 < n)` (theorem): hn follows from hqn : ¬ (q:ℕ) ∣ n. If n = 0 then (q:ℕ) ∣ 0 (dvd_zero), contradicting hqn, so n ≠ 0 and hence 0 < n. (hα also gives it: α^0 = 1 = (q:ℂ-bar) is impossible since q ≥ 2 in characteristic 0.) hn is not mentioned in any other binder or in the conclusion. The proof only needs it in `Nat.mul_pos hn hd`, `zero_pow hn.ne'`, `NeZero n` and `hn.ne'`. Inside the proof, derive it first with `have hn : 0 < n := Nat.pos_of_ne_zero (fun h => hqn (h ▸ dvd_zero _))`. The rest of the proof is unchanged, so the theorem is true and provable without the argument.

### [`P2MW.S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.PLCDSol.exists_gamma0_apply_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_principal_le_closure_divisor_laurentIntegral_diamondAutHBar.lean#L883-L889) — `flt-anthropic-0048`

Snippet: `samples/flt-anthropic/flt-anthropic-0048.lean`

- `[NeZero M]` (variable): The statement (∃ γ : SL(2,ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = d, for d : (ZMod M)ˣ) elaborates for every M, since ZMod M is a CommRing for all M. The only use of NeZero M is that the proof calls CohCarrier.gamma0Units_surjective, which has a [NeZero M] argument. The statement is still true for M = 0. There ZMod 0 = ℤ, Gamma0 0 is the set of matrices with c = 0, and the units of ℤ are d = ±1. Take γ = d • I, which has det d² = 1, lies in Gamma0 0, and has γ 0 0 = d. For M ≠ 0 the existing proof works. So the proof can split on M = 0, or use surjectivity of SL(2,ℤ) → SL(2,ZMod M), and the NeZero M argument can be dropped. The variable H is not an argument of this theorem, because the statement does not mention it and the section has no include.

### [`P2MW.S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.CohCarrier.gammaH_inf_gamma0_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_relfinrank_qExpFunctionFieldC_gammaH_gammaH_inf_gamma0_mul_eq_add_one.lean#L104-L128) — `flt-anthropic-0049`

Snippet: `samples/flt-anthropic/flt-anthropic-0049.lean`

- `[NeZero N]` (theorem): Nothing in the statement needs it. CohCarrier.GammaH M H is defined as (H.comap (gamma0Units M)).map (Gamma0 M).subtype, and gamma0Units, Gamma0Map and Gamma0_d_mul_a are stated for an arbitrary M : ℕ (`variable (M : ℕ)` in Definitions/Def_CohCarrier_Level.lean, with no NeZero). Gamma0 and ZMod.unitsMap also need no NeZero. The proof is uniform in N: it uses only mem_GammaH_iff, Gamma0_mem, the cast ring hom ZMod.castHom (dvd_mul_right N ℓ) (ZMod N) with map_intCast, and simp lemmas. It never uses NeZero. For N = 0, ZMod 0 = ℤ and the same argument still works. The hypothesis is also implied by [NeZero (N*ℓ)], since N*ℓ ≠ 0 forces N ≠ 0.
- `[NeZero (N * ℓ)]` (theorem): Nothing in the statement needs it. GammaH, Gamma0, gamma0Units and ZMod.unitsMap are all defined for arbitrary natural-number levels with no NeZero. The proof never uses it: it only uses mem_GammaH_iff, Gamma0_mem, ZMod.castHom and map_intCast, and these work for any N and ℓ (ZMod 0 = ℤ is fine). Deleting it leaves the statement true with the same proof. Each of the two NeZero hypotheses can be deleted on its own, and both can be deleted together.

### [`TateCurve.pointX_inv_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_TateCurve_XMultStructure.lean#L171-L175) — `flt-anthropic-0057`

Snippet: `samples/flt-anthropic/flt-anthropic-0057.lean`

- `(hu0 : u ≠ 0)` (theorem): The hypothesis is only used to show u * v⁻¹ ≠ 0 for `pointX_inv`. If u = 0 (or v = 0), then u⁻¹ * v = 0 and u * v⁻¹ = 0 (using inv_zero), so both sides are `pointX q 0` and the goal is `rfl`/`simp`. The rewrite u⁻¹ * v = (u * v⁻¹)⁻¹ holds in any field. A proof by cases works: if u * v⁻¹ = 0, then after the rewrite `(u*v⁻¹)⁻¹ = 0⁻¹ = 0` and the goal closes by `simp`. Otherwise u * v⁻¹ ≠ 0, so `pointX_inv hq0 h hdiv` applies. The other hypotheses still give `pointX_inv` its needed inputs. hu0 and hv0 can be deleted together, because the single case split on u * v⁻¹ = 0 replaces both.
- `(hv0 : v ≠ 0)` (theorem): The hypothesis is only used to show u * v⁻¹ ≠ 0 for `pointX_inv`. If v = 0 (or u = 0), then u⁻¹ * v = 0 and u * v⁻¹ = 0, so both sides are `pointX q 0` and the statement is trivially true. A proof splits on u * v⁻¹ = 0. In the zero case, rewrite u⁻¹ * v as (u*v⁻¹)⁻¹, which is 0⁻¹ = 0, and close by simp. In the nonzero case, apply `pointX_inv hq0 h hdiv`. hu0 and hv0 can be deleted together, because this single case split replaces both.

### [`P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.Nat.not_mem_placesOf_of_mem_placesOf_of_coprime`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin.lean#L72-L74) — `flt-anthropic-0058`

Snippet: `samples/flt-anthropic/flt-anthropic-0058.lean`

- `(hℓ : ℓ ≠ 0)` (theorem): placesOf is defined as `if h : span {(ℓ : 𝓞 ℚ)} = ⊥ then ∅ else ...`. For ℓ = 0, the span of {0} is ⊥ (Ideal.span_singleton_eq_bot), so placesOf 0 = ∅. Then `hv : v ∈ placesOf 0` is absurd and the conclusion holds vacuously. For ℓ ≠ 0 the existing proof works. Proof: `rcases eq_or_ne ℓ 0 with rfl | hℓ`; the first case closes by simp [placesOf] at hv (or exfalso); the second uses the old argument. Can be deleted on its own, and also together with hℓ'.
- `(hℓ' : ℓ' ≠ 0)` (theorem): For ℓ' = 0, placesOf 0 = ∅ because span {0} = ⊥ makes the `dif_pos` branch give ∅. So `v ∉ placesOf 0` holds trivially. For ℓ' ≠ 0 the existing proof works, using disjoint_placesOf_of_coprime. Proof: case split on ℓ' = 0; in the zero case use simp [placesOf]. Can be deleted on its own, and also together with hℓ, since ℓ = 0 is handled by the vacuous case.

### [`P2MW.S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.P2mLocalIndex.main`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one.lean#L843-L876) — `flt-anthropic-0059`

Snippet: `samples/flt-anthropic/flt-anthropic-0059.lean`

- `(hn : ‖n‖ = 1)` (theorem): hn is implied by hm except in one case, and in that case the conclusion holds trivially. (1) If m ≥ 1, then ‖1-n‖ = q^{-m} < 1 because q = absNorm v > 1. By the ultrametric inequality ‖n‖ = ‖1-(1-n)‖ = 1. (2) If m = 0, then ‖1-n‖ = 1. If ‖n‖ > 1, then ‖1-n‖ = ‖n‖ > 1, a contradiction, so ‖n‖ ≤ 1. If ‖n‖ = 1, the existing proof applies. If ‖n‖ < 1 (including n = 0), the conclusion is Ideal.absNorm v.asIdeal ^ min s 0 = 1, and it holds. By hc, v(c)^f = v(n) < 1, using that θ preserves the valuation, so ‖c‖ < 1. This follows from v_theta_eq_one for units, extended to all y by writing y as algebraMap(ϖ^k) times a unit, since θ fixes the base field. For ‖y‖ > 1 we get ‖θ y‖ = ‖y‖ > ‖c y‖, so ‖θ y - c y‖ = ‖y‖ > 1. Hence {y : (θ-c)y ∈ O} ∩ {y : π^s y ∈ O} = O, and the relative index of O in O is 1 = q^{min(s,0)}. The ‖n‖ < 1 case needs a separate short argument. So hn can be dropped, because m = 0 with n a non-unit gives index 1 anyway, and the proof would first derive hn1 by case analysis on m.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L610-L612) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- `[CharZero L]` (variable): The statement is `HahnSeries.C c = algebraMap L (LaurentSeries L) c` for `c : L`. It needs only `Field L` to elaborate. `CharZero L` is a section variable that the theorem takes only because its type mentions `L`. The proof is `rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]`. `ModularCurve.algebraMap_laurentSeries_eq_single` is stated in `Definitions/Def_ModularCurve_LaurentCoeff.lean` under `variable (L : Type*) [Field L]`, with no characteristic assumption. `HahnSeries.C_apply` needs no assumption on `L` beyond a semiring. So the proof does not use `CharZero L`. The identity holds in every characteristic, including positive characteristic. Deleting the argument with `omit [CharZero L] in` (alongside the existing `omit [NeZero m] in`) leaves the statement true and the proof unchanged.

### [`P2MW.S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.W8O.ramificationIndex_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_forall_normFormulaAlong_of_isAlgClosed_of_charP_pos.lean#L169-L198) — `flt-anthropic-0064`

Snippet: `samples/flt-anthropic/flt-anthropic-0064.lean`

- `[CharP M p]` (variable): The statement `w.ramificationIndex M = p ^ r`, together with `hrange`, only needs `CharP E p` (for `iterateFrobenius E p r`) and the other field and algebra data. `CharP M p` does not appear in the statement. It is used only inside the proof, and only through `theta`, which needs `ExpChar M p`. The hypothesis follows from `[CharP E p]` and the injective ring hom `algebraMap M E` (injective because `M` is a field): Mathlib has `RingHom.charP (f : R →+* A) (H : Function.Injective f) (p) [CharP A p] : CharP R p` in Mathlib/Algebra/CharP/Algebra.lean. So the theorem can use `omit [CharP M p] in` and start the proof with `haveI : CharP M p := (algebraMap M E).charP (algebraMap M E).injective p`. The rest of the proof is unchanged. The only other use I found, at line 254, still has `CharP M p` in scope from the `variable` line.

### [`P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.lean#L2414-L2438) — `flt-anthropic-0066`

Snippet: `samples/flt-anthropic/flt-anthropic-0066.lean`

- `(ha2 : a ^ (q ^ 2) = a)` (theorem): The proof never uses ha2. It builds θ from `red` and then closes the goal with `ModularCurve.C4b.core θ f h₁ h₁F h₁0 a ha hsupp`. That lemma, at line 2185 of the same file, takes no hypothesis of the form a^(q^2)=a. Its other arguments are the same ones the theorem already has: ha : a ∉ ssJSet q k, hsupp, h₁, h₁F and h₁0. The conclusion does not mention ha2 either. Deleting ha2 therefore leaves the theorem true, with the proof unchanged.

### [`P2MW.S_CohCarrier_isEis_kernel_pair_of_prime.CohCarrier.IsEisKernelPairPrime.exists_crt`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_isEis_kernel_pair_of_prime.lean#L359-L443) — `flt-anthropic-0072`

Snippet: `samples/flt-anthropic/flt-anthropic-0072.lean`

- `[NeZero P]` (theorem): The statement does not need it: `mapN n` is defined for every `n : ℕ` as `Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))` and takes no `NeZero`. The proof uses `NeZero P` only to build `NeZero (P*M₁)`, which `ModularCurve.surjective_specialLinearGroup_map_zmod` requires. Without the hypothesis, split on `P = 0`. If `P = 0`, then `Nat.Coprime 0 M₁` forces `M₁ = 1`. Take `g₁ = g`. The first goal is `rfl`. The second holds because `SL(2, ZMod 1)` is a subsingleton (`ZMod 1` is trivial, so the matrices and then the `SL` elements are equal). If `P ≠ 0`, the existing proof applies, with `NeZero P` obtained from `P ≠ 0`. The other instance `[NeZero M₁]` is still available in that branch, so `NeZero (P*M₁)` follows as before. This hypothesis can be deleted on its own, and it can also be deleted together with `[NeZero M₁]` (see the other entry).
- `[NeZero M₁]` (theorem): The statement does not need it, for the same reason: `mapN` has no `NeZero` requirement. Without the hypothesis, split on `M₁ = 0`. Then `Nat.Coprime P 0` forces `P = 1`. Take `g₁ = 1`. The first goal, `mapN 1 1 = mapN 1 g`, holds because `SL(2, ZMod 1)` is a subsingleton. The second goal, `mapN 0 1 = 1`, is `map_one`. If `M₁ ≠ 0`, the existing proof applies, with `NeZero M₁` obtained from `M₁ ≠ 0`. The other instance `[NeZero P]` is still available in that branch, so `NeZero (P*M₁)` follows as before. This hypothesis can be deleted on its own, and it can also be deleted together with `[NeZero P]`. In the both-deleted case, split into the cases `P = 0`, `M₁ = 0`, and both nonzero.

### [`P2MW.S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.Loc4Sol.residual_isEquiv_point`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_not_dvd_level_and_not_isUnit_qCoeff_of_point_of_not_isOrdinaryAt.lean#L165-L200) — `flt-anthropic-0088`

Snippet: `samples/flt-anthropic/flt-anthropic-0088.lean`

- `(habs : ρbar.IsAbsolutelyIrreducible)` (theorem): habs is used only to get `habs.baseChangeAlong φk`, i.e. absolute irreducibility of `ρbar.baseChangeAlong φk`. That is already implied by habs' and the charpoly equality `hall` that the proof builds. Mathlib-free library lemma `ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq (ρ₁ ρ₂ : ResidualGaloisRep k) (h₁ : ρ₁.IsAbsolutelyIrreducible) (hcp : ∀ σ, (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly) : ρ₂.IsAbsolutelyIrreducible` (Theorems/Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq.lean) applies with ρ₁ := ρ'.residual, ρ₂ := ρbar.baseChangeAlong φk, h₁ := habs' and hcp := hall. `hall` is the same fact that is already passed to `isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq`, so its type fits. The final step then becomes `isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq _ _ habs' (isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq _ _ habs' hall) hall`. habs appears nowhere else in the statement, so it can be deleted without changing the rest.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.K45VolB3.iterate_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.lean#L218-L220) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- `[NumberField L]` (variable): The variable `[NumberField L]` becomes an argument because its type mentions only `L` and `[Field L]`, which are already arguments. The statement never uses it. `σE` is `AutomorphicForm.sigmaTensor K L Kv σ`, and `sigmaTensor` is declared with only `[Field K] [Field L] [Algebra K L] [CommRing A] [Algebra K A]`. The type `L ⊗[K] Kv` needs nothing about `L` beyond that. The `NumberField K` instance is what `HeightOneSpectrum.adicCompletion K v` needs, via `IsDedekindDomain (𝓞 K)`, and that stays. The proof rewrites with `sigmaTensor_pow`, which is stated in the same file under `Field K`, `Field L`, `Algebra K L`, `CommRing A` and `Algebra K A` only, and then uses `map_mul` for the ring hom `σE`. So the proof goes through unchanged without `NumberField L`. The theorem is true without it, because the identity holds for any ring homomorphism. The author already omitted `[IsGalois K L]` here and left `[NumberField L]` in.

### [`P2MW.S_ModularCurve_PDPairing_index_Gamma_four.ModularCurve.PDPairing.TD.pairF_res_cores_normal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PDPairing_index_Gamma_four.lean#L5591-L5659) — `flt-anthropic-0095`

Snippet: `samples/flt-anthropic/flt-anthropic-0095.lean`

- `[Γ'.FiniteIndex]` (theorem): The statement does not need it. `cores hΦΓ` only requires `[Φ.FiniteIndex]` (see its definition: `{Φ' Φ} (h : Φ' ≤ Φ) [Φ'.FiniteIndex]`, with Φ' = Φ here). `res` and `pairF Φ` take no finite-index hypothesis on Γ'. The hypothesis is also implied by `hΦΓ : Φ ≤ Γ'` and `[Φ.FiniteIndex]`, via Mathlib's `Subgroup.finiteIndex_of_le : [H.FiniteIndex] → H ≤ K → K.FiniteIndex`. The proof only needs it, if at all, for `Fintype (Γ' ⧸ K)`, and that is supplied by `haveI := Subgroup.finiteIndex_of_le hΦΓ`. The other steps (`pairF_transport`, `isPar_res`, `pairF_sum_left`, `coresFun_eq`) do not use finite index of Γ'. The theorem stays true and provable after deleting the binder.

### [`P2MW.S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul.lean#L99-L202) — `flt-anthropic-0099`

Snippet: `samples/flt-anthropic/flt-anthropic-0099.lean`

- `(hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)` (theorem): No name in the statement refers to hcover, and the proof never uses it. The proof only uses hn, hn0 (finiteness of the pullback), hne₁ (nonemptiness of U), he₁, Mdl₁ and the lemmas about Pic0 closures. Deleting it leaves the statement unchanged, and the proof as written still goes through. The statement is also still true, because the proof gives it without this hypothesis.
- `(hred : IsReduced (pullback i₁.1 i₂.1))` (theorem): It appears in no other binder or in the conclusion, and the proof never uses it. It is a class-typed local hypothesis, but nothing in the proof needs an IsReduced instance. Finiteness comes from `Nat.finite_of_card_ne_zero` with hn and hn0. The proof is unchanged without it.
- `(hM : 5 ≤ M)` (theorem): hM is not used in the proof or by any other binder. It is a plain Prop, not a class, so instance resolution cannot pick it up. The statement and proof use only the objects built from M, namely `igusaFunctionFieldX1C k M w` and `Mdl₁`. Deleting it leaves the proof unchanged.
- `(hpM : ¬ p ∣ M)` (theorem): It is a plain Prop that is never referenced in the statement or the proof, and it is not a class instance. Deleting it leaves the proof unchanged.
- `(hζ : IsPrimitiveRoot ζ p)` (theorem): It is never referenced in the proof or the rest of the statement, and it is not a class. Deleting it leaves the proof unchanged.
- `(hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))` (theorem): K is a free variable, so the rest of the statement still elaborates without hK, and the proof never uses the equation. The argument only needs the structure carried by Mdl₁, i₁, i₂ and hne₁.
- `(hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)` (theorem): It is a plain Prop that is not used in the proof or in the statement elsewhere, and it is not a class. Deleting it leaves the proof unchanged.
- `(hζA : ∃ z : A, algebraMap A L z = ζ)` (theorem): It is a plain Prop that is never used in the proof, and nothing else in the statement mentions it. Deleting it leaves the proof unchanged.
- `(hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)` (theorem): j is a free variable that the rest of the statement uses only through `modelTo A K j`. Nothing in the statement refers to hj, and the proof never uses it. It is an Eq, not a class. Deleting it leaves the proof unchanged.

### [`P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.R4GC.qC_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.lean#L1440-L1442) — `flt-anthropic-0104`

Snippet: `samples/flt-anthropic/flt-anthropic-0104.lean`

- `[NeZero m]` (variable): `[NeZero m]` comes from `variable {m : ℕ} [NeZero m] {M' : ℕ}`. It is an argument only because `m` appears in the statement, and the statement does not need it. The statement is `qC f = 0 ↔ f = 0` for `f : ModularForm (Γ m M') k`.

- `Γ m M'` is `((GH m M' : Subgroup SL(2,ℤ)) : Subgroup (GL (Fin 2) ℝ))`, with `GH m M' = CohCarrier.GammaH (m^2*M') (levelH m M')`. In the sources I read, neither `GammaH` (Def_CohCarrier_Level.lean, `variable (M : ℕ)`) nor `levelH` (Def_ModularCurve_FullLevelJacobian.lean, `variable (q M' : ℕ)`) requires `NeZero`.
- The same file already has `omit [NeZero m] in theorem one_mem_strictPeriods : (1:ℝ) ∈ (Γ m M').strictPeriods` (line 273), and the lemma used in the proof depends on it. It compiles without the instance, so `Γ m M'` elaborates without `NeZero m`.
- The proof is `rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]` followed by `map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective`. Mathlib's `ModularForm.qExpansion_eq_zero_iff` (QExpansion.lean, line 627) takes only `0 < h`, `h ∈ Γ.strictPeriods` and `f : ModularForm Γ k`, with no instance on `Γ`. `one_mem_strictPeriods` needs no `NeZero m`, and the injectivity lemma is generic.

So the proof never uses `NeZero m`, and the theorem holds without it. In `m = 0` the group is `GammaH (0^2*M')`, which `strictPeriods` and `qExpansion_eq_zero_iff` handle in the same way as any other subgroup. Writing `omit [NeZero m] in` before the theorem deletes the argument.

### [`P2MW.S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_apply_eq_pi_U_of_forall_point_apply_eq_unitRoot_of_isAbsolutelyIrreducible.lean#L32-L223) — `flt-anthropic-0121`

Snippet: `samples/flt-anthropic/flt-anthropic-0121.lean`

- `(hθ : ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), θ t = θ' (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (Finset.coe_subset.mpr hS₀)) t))` (theorem): The identifier `hθ` never appears in the proof. The only similar name is `hθ'U`, which is a different hypothesis. The proof uses `hΨ` for the compatibility of Ψ with π. It uses `hθ'U`, `hu`, `hT`, `hU0`, `hU1` and `hTp` through the lemma `exists_points_jointly_injective_of_charpoly_frobenius_eq_of_isAbsolutelyIrreducible`. It never needs the relation between θ and θ'. θ is still needed to state the types of `Ψ`, `u`, `hΨ` and `hu`, so the binder θ stays. Only the equation `hθ` is removed. The statement still elaborates without it, because no later binder mentions `hθ`. The existing proof compiles unchanged after deleting `hθ`, so the theorem remains provable.

### [`P2MW.S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.M4aD2Skeleton.zetaIntegral_eq_setIntegral_theta'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe.lean#L6363-L6392) — `flt-anthropic-0122`

Snippet: `samples/flt-anthropic/flt-anthropic-0122.lean`

- `[MeasurableSpace (AdeleRing (𝓞 F) F)]` (theorem): The statement never uses a measurable space on the adele ring. `ν` lives on the units `(AdeleRing (𝓞 F) F)ˣ`, which has its own `MeasurableSpace` binder. `ideleNorm` is defined through `distribHaarChar`, which does not take measurable-space arguments on the ring (its body builds `borel A` internally). `schwartzBruhat`, `ThetaSum` and `IsFundamentalDomain` don't use it either. The only use is in the proof, where `ideleNorm_mul_principal` takes `[MeasurableSpace 𝔸] [BorelSpace 𝔸]`. That lemma uses them only because `NumberField.AdeleRing.distribHaarChar_algebraMap` takes them as arguments, and the conclusion `distribHaarChar … = 1` doesn't depend on them. The theorem can supply them itself: start the proof with `letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F; haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F`. `adeleBorel` is `borel _`, and `borelSpace_adeleBorel` is `BorelSpace.mk rfl`. Both are in Definitions/Def_NumberField_AdelicHaar.lean. The rest of the proof (`integrable_zetaIntegrand`, `integral_eq_setIntegral_tsum_smul`, `chi_mul_principal`) never touches these instances. So the statement stays true and provable without them. This and the `BorelSpace` binder below can be removed together, because the same two `letI`/`haveI` lines replace both.
- `[BorelSpace (AdeleRing (𝓞 F) F)]` (theorem): Same reasoning as for the `MeasurableSpace` binder on the adele ring. Nothing in the statement refers to a Borel structure on the ring itself; the `BorelSpace` instance needed for `ν` is the one on the units. The proof uses it only to call `ideleNorm_mul_principal`. That call can be served by `haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F`, paired with `letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F`. The quantity `ideleNorm F x` doesn't depend on these instances. So the binder can be deleted and the theorem keeps the same statement. This can be removed together with the `MeasurableSpace` binder, which the same two lines also replace.

### [`P2MW.S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.NumberField.AdelicFourier.GodementSiegelEstimate.real_bound`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_AdelicFourier_exists_forall_setIntegral_norm_le_one_tsum_norm_apply_smul_vecMul_mul_rpow_le_mul_archHeight_pow_of_mem_integralWindowedSiegelSet_rat.lean#L337-L423) — `flt-anthropic-0123`

Snippet: `samples/flt-anthropic/flt-anthropic-0123.lean`

- `(hC : 0 ≤ C)` (theorem): The statement stays true without hC. Take any r α δ H satisfying the hypotheses. The factors (1 + (rα)⁻¹^2), (1 + (rδ)⁻¹^2) and (min 1 (..) + min 1 (..)) are all ≥ 0, and the right-hand side B*(1+H)^(N+1)*r⁻¹^N is ≥ 0 for B ≥ 0, because H > 0 and r > 0. If C < 0, the left-hand side is C times a nonnegative product, so it is ≤ 0. Then B = 0 works. If C ≥ 0, the existing proof applies unchanged. The proof only changes by a case split `rcases le_or_gt 0 C`. In the negative case, give B = 0 and conclude with `mul_nonpos_of_nonpos_of_nonneg` (or nlinarith) plus nonnegativity of the right-hand side. The other hypotheses are genuinely needed. If c ≤ 0 or D ≤ 0, α can be arbitrarily small with r = 1, which makes the left-hand side unbounded relative to the right-hand side. N appears in the conclusion.

### [`P2MW.S_TateCurve_ks17_D3_exports.TateCurve.sum_mul_Fz_Fz_eq_sum_lines_nat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateCurve_ks17_D3_exports.lean#L108-L111) — `flt-anthropic-0124`

Snippet: `samples/flt-anthropic/flt-anthropic-0124.lean`

- `[IsUltrametricDist K]` (theorem): The statement is pure finite-sum algebra over a field. `Fz u a := u^a + u^(-a) - 2` is defined for any `Field K` (Definitions/Def_TateCurve_DefectLines.lean:418-420), and `Fz_zero : Fz u 0 = 0` holds there too. The proof: terms with g x = 0 or h x = 0 vanish by `Fz_zero`. The remaining x have g x, h x ∈ [1, N] by hg and hh. Group these by the pair (g x, h x) = (k, j) with `Finset.sum_fiberwise`-style regrouping and pull out the factor `Fz u k * Fz v j`. None of this uses the norm, the ultrametric inequality or completeness. `Fz` only needs the `Field` structure that `NontriviallyNormedField K` supplies, so the statement still elaborates without this instance.
- `[CompleteSpace K]` (theorem): The same argument applies: the identity is an algebraic regrouping of a finite sum, using only `Fz_zero` and the bounds hg and hh. No topology or completeness is used. `Fz` needs only the `Field` structure, so the statement still elaborates without this instance. This can be deleted independently of `[IsUltrametricDist K]`, and both can be deleted together.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal.Ψ₂Sq_𝓦p_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L273-L277) — `flt-anthropic-0125`

Snippet: `samples/flt-anthropic/flt-anthropic-0125.lean`

- `(hp2 : p ≠ 2)` (theorem): The statement stays true for p = 2. `Ψ₂Sq` is `C 4 * X^3 + C b₂ * X^2 + C (2*b₄) * X + C b₆` (Mathlib, DivisionPolynomial/Basic.lean:117). For p ≠ 2 the proof uses coefficient 3, which is 4 ≠ 0. For p = 2 use coefficient 2 instead. That coefficient is b₂ = a₁² + 4a₂ = X 0 ^ 2 + 4 * X 1 in `Rp 2`. Since 4 = 0 in ZMod 2, it equals X 0 ^ 2, which is nonzero in MvPolynomial (Fin 5) (ZMod 2) because ZMod 2 is nontrivial. Uniformly, one can apply `MvPolynomial.eval` at a₁ = 1 and all other aᵢ = 0. Then b₂ = 1, and Ψ₂Sq maps to 4X³ + X², whose X² coefficient is 1 ≠ 0 in the nontrivial ring ZMod p. A nonzero image forces Ψ₂Sq ≠ 0, so `[Fact p.Prime]` alone suffices. `Fact p.Prime` must stay: for p = 1, `Rp 1` is the trivial ring and the claim fails. The `hp2` binder is not needed to elaborate the statement; it is only used to supply `four_ne_zero_Rp`.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.AlgebraicCurve.HolRingFGAux.exists_fin_generators`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_exists_finite_generators_regular_off_ends_residueField_of_eq_three_of_dvd.lean#L590-L610) — `flt-anthropic-0132`

Snippet: `samples/flt-anthropic/flt-anthropic-0132.lean`

- `(hN : N.Nonempty)` (theorem): The statement stays true for N = ∅, so hN can be dropped. The proof would need extra work, and I have not written it out. Places are all non-trivial DVR valuation subrings of K containing k. The hypotheses force K to be a function field of trdeg 1 over the algebraically closed field k: `Algebra.EssFiniteType` makes K finitely generated, and Ω[K/k] of rank 1 forces trdeg = 1, because Ω[K/k] = 0 if K = k. For N = ∅, holRing ∅ is the intersection of all places, which is exactly k, the elements regular at every place. So the generator list n = 0, z = ![] works: the first conjunct is vacuous, and Algebra.adjoin k (range z) = ⊥ contains the image of k. Every f in the intersection is algebraic over k, hence lies in k because k is algebraically closed. The argument is as follows. If f were transcendental and in holRing ∅, then f ∈ holRing {Q} for any Q. The existing Dedekind-domain argument in `holRing_fg` shows holRing {Q} is the integral closure of k[f] in K, so it is Dedekind. Any maximal ideal (f − c) of k[f] lies under a maximal ideal of this integral closure. That gives a place where f − c is a non-unit and f has no pole anywhere. A place where t has a pole is also what `transcendental_of_not_mem` needs. So the nonempty hypothesis is only used to get `exists_fn` and a place Q₀ for transcendence, and an alternative argument covers the empty case. I am fairly but not fully certain, since the empty case needs a new proof.

### [`P2MW.S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.MapsDvdSol.opFamily_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CohCarrier_levelRaisingComb_mem_parabolicHoms_and_adjoint_and_comm_of_prime_of_dvd.lean#L343-L365) — `flt-anthropic-0134`

Snippet: `samples/flt-anthropic/flt-anthropic-0134.lean`

- `[IsDomain 𝒪]` (variable): The statement only uses `opFamily N ⊤ S 𝒪`. Its signature needs `[CommRing 𝒪]` and `[NeZero N]`, nothing else (Def_CohCarrier_Inst). The proof uses `diamondL_top_eq_one`, which is stated for any `[CommRing 𝒪]`. It also uses `CohCarrier.heckeT_comm_of_prime`, which has no assumptions on the coefficient ring beyond `[AddCommGroup V]`. `IsDomain 𝒪` is never used, and the theorem is true and provable without it. It is an argument only because it is an instance-implicit variable whose type mentions only `𝒪`. It can be dropped with `omit [IsDomain 𝒪] in`.
- `[CharZero 𝒪]` (variable): The statement and proof need only `CommRing 𝒪`. `opFamily`, `heckeTL`, `diamondL_top_eq_one` and `CohCarrier.heckeT_comm_of_prime` take no characteristic assumption. The hypothesis is an argument only because its type mentions `𝒪`. It can be omitted independently of the others.
- `[IsLocalRing 𝒪]` (variable): Nothing in the statement or proof refers to a local-ring structure. The commutation of the Hecke operators `heckeTL` holds over any commutative ring `𝒪`, because it follows from `heckeT_comm_of_prime`, which is stated for an arbitrary additive commutative group. The hypothesis is an argument only because its type mentions `𝒪`. It can be omitted independently of the others.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.C2Count.natCard_finPts`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime.lean#L214-L257) — `flt-anthropic-0143`

Snippet: `samples/flt-anthropic/flt-anthropic-0143.lean`

- `(hm : 0 < m)` (theorem): hm follows from hmp : m.Coprime p together with the variable [Fact p.Prime], which is in scope. If m = 0, then Nat.Coprime 0 p says gcd 0 p = p = 1 (Nat.coprime_zero_left). That contradicts p being prime, since p ≥ 2. So 0 < m always holds under the other hypotheses, and the theorem is equally true without hm. In the proof, hm is only used as the positivity component of the witness ⟨m, hm, hpm, _⟩ in hinj and hsurj. Replace it by a derived fact, for example `have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; have := Nat.coprime_zero_left p |>.mp hmp; exact (Fact.out : p.Prime).one_lt.ne' this)`. The rest of the proof is unchanged.

### [`P2MW.S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.ModularCurve.SmoothedFundamentalProof.finite_support_smul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_contDiff_and_finsum_smoothedFundamental_eq_one.lean#L435-L442) — `flt-anthropic-0144`

Snippet: `samples/flt-anthropic/flt-anthropic-0144.lean`

- `[Γ.FiniteIndex]` (variable): The statement does not need it. `ModularCurve.smoothedFundamental` is defined with a `finsum` over `SL(2,ℤ) ⧸ Γ` (Def_ModularCurve_SmoothedFundamental.lean:170), so it elaborates for any subgroup. `Function.support`, `Finite` and the action of Γ on ℍ do not use finite index either. Only the proof uses it, via `mem_carrier_of_ne_zero` and `isCompact_carrierH`, which go through `smoothedFundamental_eq_sum` and need `Fintype (SL(2,ℤ) ⧸ Γ)`. The statement is still true without it. Let K = {τ}. By `finite_moving` (which has no index hypothesis), S = {δ : SL(2,ℤ) | δ•τ ∈ box T} is finite, where `box T` is the compact set from the definitions file. Suppose γ ∈ Γ and F(γ•τ) ≠ 0, where F = smoothedFundamental Γ T. Then the finsum is ≠ 0, so some term `puCut T (mob (Quotient.out q) (γ•τ))` is ≠ 0. This follows from `finprod_mem_eq_one_of_forall_eq_one`/`finsum_eq_zero_of_forall_eq_zero`, or from `exists_ne_one_of_finprod_mem_ne_one` in additive form. By `support_puCut_subset` and `mob_mob`/`coe_smul`, (Quotient.out q * γ)•τ ∈ box T, so δ := out q * γ lies in S. Since γ ∈ Γ, the coset of δ is q. So out q = out ⟦δ⟧, and γ = (out ⟦δ⟧)⁻¹ * δ is determined by δ. The support is therefore contained in the image of the finite set S under δ ↦ (out ⟦δ⟧)⁻¹ δ, restricted to Γ, and it is finite. This is a direct proof that needs no finite-index or Fintype assumption. The degenerate case of infinite index causes no trouble, because the finsum only sums over the finitely many q with nonzero terms.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.P2mFlatIsog.ringKrullDim_stalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_of_surjective_of_isFinite_pullback_snd.lean#L246-L300) — `flt-anthropic-0150`

Snippet: `samples/flt-anthropic/flt-anthropic-0150.lean`

- `[IsIntegral Y]` (theorem): The statement still elaborates without it. Nothing else in the statement depends on `IsIntegral Y`, and the proof uses it only to get domain instances on `Γ(Y,V)` for `height_comap_eq`.

The statement is still true. X is integral, so it is nonempty, reduced and irreducible. Since h is surjective, Y is nonempty and irreducible.

Set Y' = Y_red. Then Y' is integral, and Y' → Y → Spec K is still locally of finite type. Because X is reduced, h factors as X → Y' → Y. The map X → Y' is surjective, since the underlying space of Y' equals that of Y. It is finite, because on affine opens A → B kills the nilradical N of A, so A/N → B is finite.

The primes of a ring all contain its nilradical, so the stalk of Y at h(x) has the same Krull dimension as the stalk of Y' there. The stalk of Y' is the stalk of Y modulo its nilradical. So the theorem applied to Y' gives the statement for Y.

The proof changes in one place: one works with Γ(Y,V)/nilradical in place of Γ(Y,V), or reduces to Y_red as above. Since the nilradical maps to 0 in the reduced X, injectivity of φ becomes injectivity on the quotient, and `height_comap_eq` then applies with the domain hypothesis satisfied.

I only checked that `IsIntegral Y` is removable. I did not conclude the same for `LocallyOfFiniteType fY`, because fX and fY are unrelated in the statement.

### [`P2MW.S_CuspidalType_sum_character_mul_character_inv.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspidalType_sum_character_mul_character_inv.lean#L10-L30) — `flt-anthropic-0154`

Snippet: `samples/flt-anthropic/flt-anthropic-0154.lean`

- `[CharZero K]` (theorem): CharZero is only used to show (Nat.card (GL2 q) : K) ≠ 0 so that Mathlib's `char_orthonormal` (which needs `Invertible (Nat.card G : K)`) applies. The theorem stays true without it. Case 1: the cast of |G| is nonzero in K. Then `invertibleOfNonzero` gives the instance and the existing proof goes through unchanged. Case 2: the cast of |G| is 0 in K, so the RHS is 0. Let M = V ⊗ V* with the induced G-action, and let e = Σ_g ρ_M(g). The character of M at g is χ(g)·χ(g⁻¹). Also e² = |G|·e = 0, so e is nilpotent and trace(e) = 0. Hence Σ_g χ(g)χ(g⁻¹) = 0, which equals the RHS. This argument needs V finite-dimensional, which is available (and see the FiniteDimensional entry). So CharZero can be dropped. IsAlgClosed is still needed in case 1.
- `[FiniteDimensional K V]` (theorem): Finite-dimensionality follows from hirr, Nontrivial V and finiteness of GL2 q. Pick v ≠ 0 in V. The span of the finite orbit {ρ g v : g ∈ GL2 q} is a nonzero subrepresentation, because it is invariant under ρ. By hirr it equals ⊤. So V is spanned by finitely many vectors and is finite-dimensional. Thus the instance can be derived inside the proof (via `Module.Finite.of_...` / `FiniteDimensional.span_of_finite` on the finite orbit) and does not need to be a hypothesis. The rest of the proof is unchanged. `Representation.character` is defined with trace, but the statement is true as stated either way, and the instance is recovered before `char_orthonormal` is applied.

### [`P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.R4ODGlue.eq_of_proj_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormalODModule_exists_map_eq_and_exists_isIso_of_pullback_of_surjective.lean#L415-L421) — `flt-anthropic-0167`

Snippet: `samples/flt-anthropic/flt-anthropic-0167.lean`

- `(hcomm : q'.comp p' = q''.comp p'')` (variable): hcomm is not needed. The statement still elaborates without it, because q' and q'' still appear in hpb. Take b₁, b₂ with p' b₁ = p' b₂ and p'' b₁ = p'' b₂, and let d = b₁ - b₂. Then p' d = 0 and p'' d = 0, because ring homomorphisms are additive. Also p' 0 = 0 and p'' 0 = 0. The pair (0,0) satisfies q' 0 = q'' 0, since both sides are 0. So hpb 0 0 gives a unique b with p' b = 0 ∧ p'' b = 0. Both d and 0 satisfy this, so d = 0 and b₁ = b₂. The proof would apply `hpb 0 0 (by simp)` and use uniqueness for d and 0, then `sub_eq_zero`. The current proof uses hcomm only to show that (p' b₁, p'' b₁) lies in the pullback condition, and the argument above avoids that step. hpb is still required. To delete hcomm, use `omit hcomm in`.

### [`P2MW.S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.SolCHint.ChartData.V_eq_O`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isProper_surjective_isOpenImmersion_isIntegral_isIso_morphismRestrict_of_isIntegral.lean#L489-L504) — `flt-anthropic-0182`

Snippet: `samples/flt-anthropic/flt-anthropic-0182.lean`

- `[LocallyOfFiniteType f]` (variable): The statement `D.V k = D.O k` does not mention this instance. It only enters the proof through lemmas like `V_nonempty`, `nonempty_O` and `isProper_ek`, which take it because it is a section variable. It follows from `D : ChartData f` itself. `D.U` covers `X` (`hcov : ⨆ k, U k = ⊤`). For each `k`, `(D.U k).ι ≫ f = D.c k ≫ awayι₀ ≫ ProjSpace.π A (D.e k)` by `hover`. Here `D.c k` is a closed immersion (`hc`), `awayι₀` is an open immersion (`Proj.awayι`), and `ProjSpace.π` is proper (`isProper_π` in Definitions/Def_AlgebraicGeometry_ProjSpace.lean). Proper includes locally of finite type, and closed and open immersions are locally of finite type. Locally-of-finite-type is stable under composition, so each `(D.U k).ι ≫ f` is locally of finite type. `IsZariskiLocalAtSource.iff_of_iSup_eq_top` then gives `LocallyOfFiniteType f` from the cover. The proof can therefore start with `haveI : LocallyOfFiniteType f := ...` and continue unchanged. The statement stays true, and deleting this hypothesis alone is fine. It can also be deleted together with `[QuasiCompact f]`, since the derivation of compactness of `X` below does not use it.
- `[QuasiCompact f]` (variable): This instance is used only to get `CompactSpace X` in `isNoetherian_X`, and it is not mentioned in the statement. `CompactSpace X` follows from `D`. `X = ⨆ k, D.U k` is a finite union over `Fin D.m`. Each `D.U k` is compact, because `D.c k` is a closed immersion, hence a closed embedding, into the affine (so compact) scheme `Spec (Away ..)`. So `X` is compact, by `isCompact_iUnion` over the finite index. `Spec A` is quasi-separated, so Mathlib's low-priority instance `quasiCompact_of_compactSpace` (Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean, which needs `[CompactSpace X] [QuasiSeparatedSpace Y]`) gives `QuasiCompact f`. The proof can therefore start with `haveI : QuasiCompact f := ...` and continue unchanged. The statement stays true, and deleting this hypothesis alone is fine. It can also be deleted together with `[LocallyOfFiniteType f]`, since the derivation of that instance does not use quasi-compactness.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.AlgebraicCurve.AlgebraicCurve.adeleBddPrincipal_eq_comap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean#L791-L793) — `flt-anthropic-0183`

Snippet: `samples/flt-anthropic/flt-anthropic-0183.lean`

- `[HasPrincipalDivisors K F]` (theorem): The statement elaborates without it: adeleBddPrincipal, adeleBdd, globalSub and adeleSpace are defined without that class, and adeleBdd_le_adeleSpace (Def_AlgebraicCurve_AdelicIndex.lean line 96) also needs no such hypothesis. The current proof uses it only for globalSub_le_adeleSpace, to apply comap_subtype_sup_of_le_of_le, which needs both A ≤ S and B ≤ S (A = adeleBdd D, B = globalSub K F, S = adeleSpace K F). The equation comap_S(A) ⊔ comap_S(B) = comap_S(A ⊔ B) needs only A ≤ S. If x ∈ S and x = a + b with a ∈ A, b ∈ B, then b = x − a ∈ S, so x is a sum of an element of comap_S(A) and an element of comap_S(B). The reverse inclusion holds for any submodules. A proof: apply Submodule.map_injective_of_injective with S.subtype_injective, then map_sup and map_comap_subtype, reducing to (A ⊓ S) ⊔ (B ⊓ S) = (A ⊔ B) ⊓ S. Since A ⊓ S = A, this is A ⊔ (B ⊓ S) = (A ⊔ B) ⊓ S, the modular law for A ≤ S. I have not confirmed Mathlib's exact name (sup_inf_assoc_of_le) or compiled this. No degenerate cases arise, since the argument is purely lattice-theoretic.

### [`P2MW.S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.A1b2bGenusFF.DeuringLE.ell_sub_eq_of_forall_eq_ord`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_genusFF_modularFunctionFieldFullC_eq_genusFF_modularFunctionFieldBar.lean#L175-L187) — `flt-anthropic-0184`

Snippet: `samples/flt-anthropic/flt-anthropic-0184.lean`

- `(hf0 : f ≠ 0)` (theorem): The statement stays true without hf0 because of the junk value `Place.ord 0 = 0`. This is `Place.ord_zero`, from `def ord (f : F) : ℤ := -(WithZero.log (v.adicValuation f))`, in Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean. `Divisor K F` is `Place K F →₀ ℤ`.

Proof without hf0: split on `f = 0`.
- If `f = 0`, then `hP v : P v = v.ord 0 = 0` for every `v`. So `P = 0` by `Finsupp.ext`, and `E - P = E` by `sub_zero`. The goal `ell (E - P) = ell E` then holds by rewriting.
- If `f ≠ 0`, the existing proof applies unchanged, using the case hypothesis in place of `hf0`.

The hypothesis is used only in `mul_inv_cancel_right₀ hf0` and `inv_mul_cancel_right₀ hf0`, which are needed only for the invertibility of multiplication by `f`. Nothing else in the statement mentions it.

### [`P2MW.S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.GLUECI.eq_span_tInvChart_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_exists_curveModel_closedImmersion_pair_pFibre_cover_levelSet_singleton.lean#L2727-L2734) — `flt-anthropic-0199`

Snippet: `samples/flt-anthropic/flt-anthropic-0199.lean`

- `(ht : Transcendental κ t)` (variable): Let A = chartRing κ {t⁻¹}. It is a subalgebra of L, hence a domain. hchartInv says every element of A is aeval t⁻¹ f for some polynomial f. The statement does not mention ht. The proof uses it only through transcendental_inv, to feed eq_span_of_pow_mem and isMaximal_span_tChart_sub. The statement is still true without it, by cases on whether t is transcendental. If t is transcendental, the current proof works. If t is algebraic, then x = t⁻¹ is algebraic (IsAlgebraic.inv_iff). Take a prime 𝔮 containing x. If x ≠ 0, the minimal polynomial p = X·q + C c of x has c ≠ 0. Then c = -x·q(x) lies in 𝔮, because q(x) ∈ A. But c is a unit of κ, so 1 ∈ 𝔮, contradicting primality; this case is vacuous. If x = 0 (t = 0), hchartInv makes every element of A equal to algebraMap κ A (f.coeff 0). So every nonzero element of A is a unit and is not in 𝔮, giving 𝔮 = ⊥ = span {0} = span {t⁻¹}. The degenerate cases t = 0 and trivial κ are covered. hchartInv must stay, since chartRing is an integral closure that can be bigger than κ[t⁻¹]. The proof becomes by_cases ht : Transcendental κ t, with the existing proof in the first branch and the argument above in the second.

### [`P2MW.S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.HeckeGammaH.sum_slash_beta_eq_heckeU_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean#L381-L463) — `flt-anthropic-0201`

Snippet: `samples/flt-anthropic/flt-anthropic-0201.lean`

- `(B : BezoutData M ℓ)` (theorem): B is mentioned nowhere in the statement. Only the proof uses it, through gammaInf H B, rhoInf B and bijective_option. It can be rebuilt from ρ and hρ. `BezoutData M ℓ` is just a structure holding u v : ℤ with u*ℓ + v*M = 1. Write ρ = [[a,b],[c,d]] with a*d - b*c = 1. Since ρ ∈ Gamma0 M, we have M ∣ c, say c = M*c'. By hρ, d ≡ ℓ mod M, say d = ℓ + M*m. Then a*ℓ + M*(a*m - b*c') = a*(d - M*m) + M*(a*m - b*c') = a*d - M*b*c' = a*d - b*c = 1. So ⟨a, a*m - b*c', _⟩ is a valid BezoutData, and the proof can start with `obtain`/`let` of this B (or use `exists_bezoutData`, since ℓ ∤ M follows from hρ). The rest of the proof is unchanged, because hρ is already used with rhoInf B only through the equation (ρ 1 1 : ZMod M) = ℓ. The theorem therefore stays true and provable without B as an argument.

### [`P2MW.S_PowerSeries_dvd_of_forall_taylorShift_order_le.CuspDisc.Bdd.mul_small`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PowerSeries_dvd_of_forall_taylorShift_order_le.lean#L132-L135) — `flt-anthropic-0231`

Snippet: `samples/flt-anthropic/flt-anthropic-0231.lean`

- `(hC : 0 ≤ C)` (theorem): It follows from hP : Bdd C P. Bdd C P unfolds to ∀ k, ‖coeff k P‖ ≤ C, so C ≥ ‖coeff 0 P‖ ≥ 0. Replace the hypothesis in the proof with `have hC : 0 ≤ C := (norm_nonneg _).trans (hP 0)`. The rest of the proof is unchanged, and the statement stays the same.
- `(hC' : 0 ≤ C')` (theorem): It follows from hQ : Small ρ C' m Q, which unfolds to ∀ k, ‖coeff k Q‖ ≤ C' * ρ^(m-k). Taking k = m gives ‖coeff m Q‖ ≤ C' * ρ^0 = C', so C' ≥ 0. This holds even when ρ = 0, because 0^0 = 1. Replace the hypothesis in the proof with `have hC' : 0 ≤ C' := (norm_nonneg _).trans (by simpa using hQ m)`. The rest of the proof is unchanged. Each of hC and hC' can be deleted on its own, and both can be deleted together, since each is derived from hP or hQ alone.

### [`P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.EtaleCoordK1a.rankAtStalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean#L13-L24) — `flt-anthropic-0236`

Snippet: `samples/flt-anthropic/flt-anthropic-0236.lean`

- `[Module.FinitePresentation S M]` (theorem): The proof only uses these two instances to show that p ↦ rankAtStalk M p is locally constant, so it can be moved to the generic point ⊥. That step can be skipped. For any prime p of the domain S, p.primeCompl ≤ nonZeroDivisors S, because 0 ∈ p. So the same two rewrites the proof already applies at ⊥ work at p. IsLocalization.rank_eq gives rank_{S_p}(M_p) = rank_S(M_p). IsLocalizedModule.rank_eq, applied to LocalizedModule.mkLinearMap p.primeCompl M, gives rank_S(M_p) = rank_S M = n. Hence rank_{S_p}(M_p) = n, and rankAtStalk M p is defined as Module.finrank (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M). So it equals n by Module.finrank_eq_of_rank_eq. No finite presentation is needed. The statement stays true. IsDomain is still needed: for S = k×k and M = k×0 the rank is 0 but a stalk has rank 1. This can be deleted together with the Flat hypothesis.
- `[Module.Flat S M]` (theorem): Flatness is used only to apply Module.isLocallyConstant_rankAtStalk and move from p to ⊥. The rank-of-localization lemmas (IsLocalization.rank_eq and IsLocalizedModule.rank_eq, which need only p.primeCompl ≤ nonZeroDivisors S) hold directly at every prime p of a domain. So rankAtStalk M p = finrank of the localized module = toNat of rank S M = n, with no flatness. It can be deleted, also together with FinitePresentation.

### [`P2MW.S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.SupersingularTop3.mem_of_ord_nonneg`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_seven_le_ordDiff_D_jqModC_of_ord_eq_six.lean#L40-L46) — `flt-anthropic-0240`

Snippet: `samples/flt-anthropic/flt-anthropic-0240.lean`

- `(hf : f ≠ 0)` (theorem): Place.ord is defined in Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean as -(WithZero.log (v.adicValuation f)), and `ord_zero : v.ord (0 : F) = 0` holds (line 125). If f = 0, the conclusion is `0 ∈ w.toValuationSubring`, which is true by `zero_mem`. So the statement is true without hf. The proof becomes `by_cases hf : f = 0; · subst hf; exact zero_mem _` followed by the existing argument for f ≠ 0. The existing argument is where hf was used (for `exists_unit_mul_zpow`).

### [`P2MW.S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_isTwoKernel_X_sub_C_coordsOrZero_of_addOrderOf_eq_two.lean#L16-L30) — `flt-anthropic-0249`

Snippet: `samples/flt-anthropic/flt-anthropic-0249.lean`

- `[W.IsElliptic]` (theorem): The statement never needs it. `W.toAffine.Point` and its `AddCommGroup` structure (needed for `addOrderOf`) require only `[Field F] [DecidableEq F]`. In Mathlib's Affine/Point.lean, `IsElliptic` appears only in the section `IsElliptic`, which is about `nonsingularPointEquiv`/`pointEquiv`. `coordsOrZero` is defined for any `Affine R` with `CommRing R`. `IsTwoKernel` is defined for any `CommRing T` and any `WeierstrassCurve T`, with no ellipticity. The proof never uses the instance: it uses `natDegree_X_sub_C`, `coeff_sub`, and `WeierstrassCurve.eval_Psi2Sq_of_two_nsmul_eq_zero`. That lemma takes only `[Field F] [DecidableEq F]`, `W : Affine F`, a nonsingularity proof and `2 • P = 0`, and has no `IsElliptic` assumption. The theorem therefore stays true and provable with the same proof once `[W.IsElliptic]` is deleted.

### [`P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.QMHecke12.exists_generator`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.lean#L368-L422) — `flt-anthropic-0252`

Snippet: `samples/flt-anthropic/flt-anthropic-0252.lean`

- `(hι : Function.Injective ι)` (variable): The proof of `exists_generator` never uses `hι`; it only appears in the `include hqq' hB hΛ hι hℓ in` line. Injectivity of `qmPeriodMap ι τ` comes from `QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hO ha hb ι τ`. That lemma takes only `IsOrder Λ`, `a ≠ 0`, `b ≠ 0`, `ι` and `τ`, with no injectivity hypothesis on `ι`. The other lemmas used also do not need it: `qmPeriodMap_mul` has no hypotheses on `ι`, `exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt` takes `hqq' hB Λ hΛ ℓ hℓ J ...`, and `exists_isUnitOf_nrd_eq_neg_one` takes `hB Λ hΛ`. The statement is unchanged without `hι`, since `ι` still appears in it. `hι` is not instance-implicit, so dropping it from the `include` line removes it as an argument, and the proof compiles unchanged. (`hι` is genuinely used in the sibling lemma `homothety`, via `det_eq_nrd_of_injective`, but not here.)

### [`P2MW.S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.AlgebraicCurve.AlgebraicCurve.Place.stichtenothGenusExists_of_isFractionRing`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_TranscendenceTower_degree_poleDivisor_eq_finrank.lean#L2159-L2166) — `flt-anthropic-0261`

Snippet: `samples/flt-anthropic/flt-anthropic-0261.lean`

- `[HasPrincipalDivisors K F]` (variable): The theorem takes this instance automatically from `variable [FiniteDimensional E F] [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]`, because K and F are already arguments. The theorem also has its own binder `[IsCurveOver K F]`. In `Definitions/Def_AlgebraicCurve_IsCurveOver.lean`, `class IsCurveOver : Prop extends HasPrincipalDivisors K F`, and a class's parent projection is an instance. So `HasPrincipalDivisors K F` is already implied by `[IsCurveOver K F]` and can be omitted (`omit [HasPrincipalDivisors K F] in`). The statement `StichtenothGenusExists K F` does not mention the instance, and the proof only passes it implicitly to `hasPoleDivisorPackage_of_isFractionRing`. That lemma still gets the instance by synthesis from the local `IsCurveOver K F`. `HasPoleDivisorPackage K F` and `StichtenothGenusExists K F` are Props that do not depend on the instance term, so nothing else changes.

### [`P2MW.S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.WeierstrassCurve.WeierstrassCurve.ModularCurve.kw_transcendental_polyToFunctionField_X_over_baseGeneralNoAC`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean#L3405-L3408) — `flt-anthropic-0263`

Snippet: `samples/flt-anthropic/flt-anthropic-0263.lean`

- `[W.IsElliptic]` (variable): The statement `Transcendental F (polyToFunctionField (W⁄F') X)` only needs `W⁄F'` (baseChange, which needs `Algebra R₀ F'`) and `Algebra F F'`. Nothing else in the context depends on `IsElliptic`: `GenusOnePlaceGate`, `IsCentred` and `AbelTheorem` take only a Field and, for the gate, DecidableEq. The proof uses `Transcendental.of_tower_top` and the local lemma `transcendental_polyToFunctionField_X`, which has no hypotheses beyond `Field F'`. That lemma is proved from `polyToFunctionField_injective`. So the theorem stays true and provable without it.
- `[CharZero F]` (variable): CharZero F is not used in the statement. The gate classes (GenusOnePlaceGate, IsCentred, AbelTheorem) need only Field and DecidableEq. The proof goes through `transcendental_polyToFunctionField_X (W := W⁄F')`, which needs no characteristic assumption, and then `Transcendental.of_tower_top`. Deleting it leaves everything else elaborating.
- `[CharZero F']` (variable): CharZero F' is likewise not used in the statement or in the proof. The helper lemma holds for any field, and the gate classes need no characteristic assumption. It can be deleted on its own.
- `[IsScalarTower R₀ F F']` (variable): Nothing in the statement refers to it. `W⁄F'` needs only `Algebra R₀ F'`, and `Algebra F (W⁄F').FunctionField` comes from `Algebra F F'`. The proof needs `IsScalarTower F F' (W⁄F').FunctionField`, which is derived from `Algebra F F'` alone. The R₀-tower is irrelevant to it. The Algebra R₀ F instance binder stays, because the F-side gate binders mention `W⁄F` and need it. Deleting this binder alone is fine.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F).toAffine]` (variable): The gate for the F-curve is not mentioned in the statement or used by the proof. The proof only concerns `W⁄F'` and the tower F → F'. Deleting it leaves the other binders well-formed. The other two F-side gate instances only depend on this one for their own types (IsCentred), so they are listed as separately removable. Each can be removed with the others kept, provided IsCentred is not kept without its gate. Delete this binder together with its IsCentred binder.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine]` (variable): This is a Prop-valued class on the F-curve and is not used in the statement or proof. It depends on the GenusOnePlaceGate (W⁄F) instance for its own type, so it must go if that gate goes. On its own it can be deleted without affecting anything else.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine]` (variable): The Abel theorem hypothesis for the F-curve is not used in the statement or proof. The conclusion concerns only transcendence of X over F in the function field of W⁄F', proved by `polyToFunctionField_injective`. It can be deleted on its own.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine]` (variable): The proof of transcendence of X over F' (`transcendental_polyToFunctionField_X`) uses only injectivity of `polyToFunctionField` and no gate or centredness assumption. The statement does not mention it. It can be deleted on its own.
- `[WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine]` (variable): Neither the statement nor the proof uses the Abel theorem for the F'-curve. The local helper lemma has no such hypothesis. It can be deleted on its own.
- `[WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F').toAffine]` (variable): The statement and the proof never use the place gate for the F'-curve. The helper lemma takes only `Field F'` and W. Deleting it alone would break the IsCentred (W⁄F') binder's type, so delete the IsCentred binder together with it. With both removed, the theorem is unchanged.

### [`P2MW.S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_restrict_action_quotient_clauses_of_isClopen_of_isConnected.lean#L229-L413) — `flt-anthropic-0266`

Snippet: `samples/flt-anthropic/flt-anthropic-0266.lean`

- `[ConnectedSpace X]` (theorem): The conclusion does not mention connectedness of X, and the proof never uses it. It appears only as an unused instance argument threaded through the helper lemmas range_ι_comp_eq_univ, exists_mem_translate, iSup_preimage_inf_eq and le_iSup_preimage_imagePreimage. I read the proof of range_ι_comp_eq_univ, the only place it could matter. That proof uses the following. (1) The finiteness of G, for isClosed_iUnion_of_finite. (2) The closedness of π.base, from IsFinite π via π.isClosedMap. (3) hsurj and horbit. (4) The clopenness of π.base '' W, which gives π.base '' W = univ because it is nonempty. This last step uses connectedness of the closed set π.base '' W's complement structure only through `hclopen.eq_univ hne`, and that comes from the complement-image argument, not from ConnectedSpace X. So no step uses ConnectedSpace X. The theorem therefore stays true and provable after deleting the binder, provided the same instance argument is also dropped from those four helper lemmas, whose proofs need no change.

### [`P2MW.S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_exists_galoisRepAdic_moduleEnd_ML_of_not_isFlatAt_strictOrdinary.lean#L203-L596) — `flt-anthropic-0267`

Snippet: `samples/flt-anthropic/flt-anthropic-0267.lean`

- `(htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)` (theorem): I found no use of `htame` in the proof. It occurs only in the binder list. The conclusion's unipotency clause, `∀ q ∈ Smin, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q`, is proved with `GaloisRepAdic.isUnipotentOnInertiaAt_twist` and `HeckeRing.isUnipotentOnInertiaAt_of_dvd_of_not_isUnramifiedAt`. The inputs to that last lemma are `hNmin`, `hq2` (built from `hN.1`, `hrS` and `hqS`) and `hmin`, and `htame` is not among them. No other step mentions it either. So the proof compiles unchanged with `htame` deleted, and the theorem stays true and provable without it. The remaining hypotheses and the rest of the statement are untouched.

### [`P2MW.S_Function_orbitCensus_of_dihedralThree_relations.P2MKcOrbitCensus.b_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean#L14-L17) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- `[Fintype X]` (variable): The statement `Function.Injective b` for `b : X → X` has no use for finiteness. Lean adds this instance as an argument only because its type mentions `X`, which is already an argument. The proof applies `b ∘ b` to `h : b x = b y` and simplifies with `hb`, so it never uses the instance. Without it the theorem is still true: `hb` gives `b (b (b x)) = x`, so `b` has a left inverse `b ∘ b` and is injective on any type. It can be removed with `omit [Fintype X] in`.
- `[DecidableEq X]` (variable): Nothing in the statement or the proof needs decidable equality. Lean adds it as an argument only because its type mentions `X`. `Function.Injective b` does not use it, and the proof is `congrArg` followed by `simpa [hb]`, which uses neither this instance nor `Fintype X`. Without the instance the theorem is still true by the left-inverse argument `b (b (b x)) = x`. It can be removed with `omit [DecidableEq X] in`. This and `[Fintype X]` can each be deleted, and both can be deleted together.

### [`P2MW.S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.KcHaarQuotientMulRight.lintegral_density_mul_comp_mul_right_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq.lean#L75-L109) — `flt-anthropic-0270`

Snippet: `samples/flt-anthropic/flt-anthropic-0270.lean`

- `[SFinite μH]` (theorem): The statement does not mention this instance. In the proof it is used only to call `measurable_density H μH`, which needs `[SFinite μH]`. The other lemmas used (`HaarQuotient.lintegral_density_mul_eq_one` and `lintegral_withDensity_eq_of_admissible`) do not take `[SFinite μH]`. The instance is derivable from the remaining hypotheses. `hH : IsClosed (H : Set G)` and `[LocallyCompactSpace G]` give `LocallyCompactSpace H` via `IsClosed.locallyCompactSpace` (Mathlib `Topology/Compactness/LocallyCompact.lean`). `H` is second countable as a subtype of the second-countable `G`, so `SigmaCompactSpace H` follows. Mathlib's instance `IsHaarMeasure.sigmaFinite [SigmaCompactSpace G] : SigmaFinite μ` (in `Group/Measure.lean`) then gives `SigmaFinite μH` from `[μH.IsHaarMeasure]`, hence `SFinite μH`. Adding `haveI := hH.locallyCompactSpace` at the start of the proof is therefore enough, and the theorem stays true and provable without this binder.

### [`P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.UqNSol.fstDiv_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean#L358-L366) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- `[hqN : Fact (¬ q ∣ N)]` (variable): This instance-implicit variable becomes an argument of `fstDiv_sum` because its type mentions only `q` and `N`, which are already arguments. The statement does not need it. `PlaceSpecialization.fstDiv` is defined in `Definitions/Def_ModularCurve_GlueData.lean` under `[Fact q.Prime] [NeZero N]` only. `PlaceSpecialization` itself also takes only `[Fact ℓ.Prime] [NeZero N]`, and its `Divisor … (modularFunctionFieldBar (N*q))` type has the same requirements. The proof is an induction on `s` that uses `Finsupp.filter_zero`, `Finset.sum_insert` and `fstDiv_add`. `fstDiv_add` is proved with `Finsupp.filter_add` and does not use `hqN` either. The theorem is just additivity of `Finsupp.filter` over a finite sum. It holds without the hypothesis, and the same proof works unchanged. Deleting it, for instance with `omit [hqN] in`, is possible.

### [`P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.LCMazur.OrdQ.span_singleton_eq_range_ordProj`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient.lean#L263-L272) — `flt-anthropic-0275`

Snippet: `samples/flt-anthropic/flt-anthropic-0275.lean`

- `(h2 : finrank A V = 2)` (theorem): h2 follows from hφ. A is a local ring, so it is nontrivial and commutative, hence satisfies StrongRankCondition. Mathlib's `LinearMap.charpoly_natDegree` (Mathlib/LinearAlgebra/Charpoly/Basic.lean:76) then gives `natDegree φ.charpoly = finrank A V` for V free and finite. By hφ, φ.charpoly = (X - C α) * (X - C β), which is a product of two monic degree-1 polynomials. Its natDegree is 2 (`Polynomial.natDegree_mul'` or `natDegree_mul`, plus `natDegree_X_sub_C`). So `finrank A V = 2` can be proved inside the proof with `have h2 : finrank A V = 2 := by rw [← LinearMap.charpoly_natDegree, hφ]; simp [natDegree_mul, X_sub_C_ne_zero]`. The rest of the proof is unchanged and uses this derived h2 when calling `exists_basis_range_ordProj`. The conclusion does not mention h2, so deleting the binder leaves the statement unchanged and still true.

### [`P2MW.S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.ChartOkAbv.abv_lt_one_iff_mem_maximalIdeal`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Annulus_chord_bounds_and_rigid_of_isAttached_both_ends_of_twist.lean#L27-L40) — `flt-anthropic-0278`

Snippet: `samples/flt-anthropic/flt-anthropic-0278.lean`

- `(ha : a ≠ 0)` (theorem): The statement does not mention `ha`. It is only used in the proof, to feed `abv_lt_one_iff_inv_not_mem` and `mul_inv_cancel₀`. The case a = 0 is also true. μ 0 = 0 < 1 by `map_zero` and `zero_lt_one`. The element ⟨0, haA⟩ equals 0 in A, and 0 lies in `IsLocalRing.maximalIdeal A` by `Ideal.zero_mem`. So both sides of the iff hold. A proof is `by_cases ha : a = 0`. In the zero case, `subst ha` and prove both sides directly. Otherwise, run the existing proof. The remaining hypotheses `haA` and `hμA` are still needed, since the statement mentions `haA` and `hμA` is what links μ to A.

### [`P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.TH1Wanted2.inv_mem_and_const_mem_of_gaussPresentation`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel_of_eq_three.lean#L874-L964) — `flt-anthropic-0285`

Snippet: `samples/flt-anthropic/flt-anthropic-0285.lean`

- `(hq3 : q = 3)` (theorem): hq3 is never used. The proof never rewrites with it or substitutes q, and it mentions only q, so no other binder or the conclusion depends on it. The proof uses `qExpand_injective` and `coeffMap_qExpand` for general q, and `qExpand`/`fieldBar` only need `Fact q.Prime`, which stays. The argument is uniform in q, so the statement is true for every prime q. Deleting hq3 leaves the same proof working.
- `(hqM' : ¬ q ∣ M')` (theorem): hqM' appears nowhere in the statement or the proof. `fieldBar q M'` is `xHFunctionFieldBar (q^2*M') (levelH q M')`, which is defined for any natural numbers. `modularFunctionFieldBar M'` and `modularFunctionField_le_full` need only `[NeZero M']`, which stays. No type depends on a proof of coprimality, and the argument never uses it, so deleting it changes nothing.
- `(hK₁ : FiniteDimensional ↥k₀ ↥K₁)` (theorem): hK₁ is never used. The statement and proof do not need finite dimensionality of K₁ over k₀. They use only that A₁ is compatible with A (`hA₁`) and the coefficient-ring structure of Laurent series over A. No instance or term in the statement mentions hK₁, because the `IntermediateField.adjoin` and `Algebra` data do not depend on it. It can be removed with the proof unchanged.

### [`P2MW.S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.P2mConormLSpace.CFE.trace_algebraMap'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_lSpace_pullbackConstants_eq_span_of_isConstantFieldExtension.lean#L193-L203) — `flt-anthropic-0287`

Snippet: `samples/flt-anthropic/flt-anthropic-0287.lean`

- `[Algebra.IsSeparable K K']` (variable): The statement `trace F F' (algebraMap K' F' k) = algebraMap K F (trace K K' k)` does not mention separability. It stays true without it, and it can be proved by cases. If `Algebra.IsSeparable K K'` holds, the existing proof applies unchanged. If not, there is some `a : K'` with `¬ IsSeparable K a`. The lemma `minpoly_algebraMap_eq_map hconst` (in the same file; it needs only `FiniteDimensional K K'`) gives `minpoly F (algebraMap K' F' a) = (minpoly K a).map (algebraMap K F)`. `Polynomial.separable_map` over the field hom then shows `algebraMap K' F' a` is not separable over F. So `¬ Algebra.IsSeparable F F'`, and Mathlib's `Algebra.trace_eq_zero_of_not_isSeparable` (Mathlib/RingTheory/Trace/Basic.lean:276, for fields with no finite-dimensionality assumption) gives `Algebra.trace F F' = 0`. The same lemma applied to `K, K'` gives `Algebra.trace K K' k = 0`, so both sides are 0. The other hypotheses are still needed. `hgen` is needed: with K'=K, F'=F(t), F=K, the left side is 0 and the right side is 1. `hconst` is needed: with K=ℚ, K'=F=F'=ℚ(√2), the left side is k and the right side is k+σk. `FiniteDimensional K K'` is needed: with K'=F=F'=ℚ(t) and K=ℚ, the left side is k and the right side is 0.

### [`P2MW.S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.solution`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.lean#L110-L138) — `flt-anthropic-0294`

Snippet: `samples/flt-anthropic/flt-anthropic-0294.lean`

- `[IsDomain A]` (theorem): IsDomain A is implied by the other hypotheses. IsFractionRing A K with K a field gives Function.Injective (algebraMap A K) (IsFractionRing.injective A K), and a ring that injects into a domain (K is a field) is a domain (Function.Injective.isDomain in Mathlib/Algebra/Ring/Hom/InjSurj.lean). The statement itself does not need it: IsIntegrallyClosed, IsLocalRing, Module.Finite, Module.Flat, IsFractionRing and ResidueField only need CommRing/CommSemiring. So the theorem stays true and elaborates without it. The only proof change is that the helper GenLift.exists_ringHom_forall_sub_mem takes [IsDomain A]. Supply it with `haveI : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)` at the start of the proof.

### [`P2MW.S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.WNormSwapSol.θ_θ_γel`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_qExpand_coe_smul_norm_heckeBetaHBar_inv_smul_eq_C_mul_prod_qTwist.lean#L941-L962) — `flt-anthropic-0295`

Snippet: `samples/flt-anthropic/flt-anthropic-0295.lean`

- `(hζ : IsPrimitiveRoot ζ p)  (together with its variable {ζ : Qbˣ})` (variable): The statement `θ (θ (γel θ)) = γel θ` does not mention ζ or hζ. They enter only through `include ... hζ`, and the proof uses them only as an auxiliary choice of a primitive p-th root. That root is passed to `map_μ_eq hpM2 hHp hθ hζ` (which proves `(μ hpM θ).map (e0 ..) = PiPoly p θ ζ`) and appears in `sv p θ ζ o`. The conclusion is independent of which primitive root is used, so the root can be produced inside the proof.

The root exists because `Qb = AlgebraicClosure ℚ` is algebraically closed of characteristic 0. Mathlib has `instance AlgebraicClosure.hasEnoughRootsOfUnity (F) [Field F] (n) [NeZero (n : F)] : HasEnoughRootsOfUnity (AlgebraicClosure F) n` in `Mathlib/RingTheory/RootsOfUnity/AlgebraicallyClosed.lean`. For F = ℚ, `NeZero (p : ℚ)` follows from `Fact p.Prime`. The lemma `HasEnoughRootsOfUnity.exists_isPrimitiveRoot` in `EnoughRootsOfUnity.lean` then gives `∃ ζ : Qb, IsPrimitiveRoot ζ p`. Since p > 0, `IsPrimitiveRoot.isUnit` makes ζ a unit, and `IsPrimitiveRoot.coe_units_iff` (already used in this file) transfers primitivity to `Qbˣ`.

So the proof would begin with `obtain ⟨ζ, hζ⟩ : ∃ ζ : Qbˣ, IsPrimitiveRoot ζ p := ...`, and the rest of the proof is unchanged. The other binders (hpM2, hHp, hθ, hd, hdH) are all needed by `θ_θ_incl` and `map_μ_eq`, so I did not flag them.

### [`P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.AlgebraicCurve.DiscRigidity.sum_filter_eq_of_degreeOn`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_disc_subset_of_eq_three_of_dvd.lean#L80-L105) — `flt-anthropic-0299`

Snippet: `samples/flt-anthropic/flt-anthropic-0299.lean`

- `(hf : f ≠ 0)` (theorem): The hypothesis is not needed, because the case f = 0 is trivial. In this library `Place.ord` is defined as `-(WithZero.log (v.adicValuation f))`, and `ord_zero` states `v.ord (0 : F) = 0` (Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean, lines 122-125). If f = 0, then `hDf` gives `Df v = v.ord 0 = 0` for every v. So Df = 0 and `Df.support = ∅`. Both filtered sums are then empty sums, equal to 0, and the statement holds. The proof would start with `rcases eq_or_ne f 0 with rfl | hf`. In the zero case, show `Df = 0` by `Finsupp.ext` with `hDf` and `Place.ord_zero`, then `simp`. The existing proof handles the nonzero case unchanged, where `hf` was used for `R.exists_smul_mem f hf` and `ord_algebraMap_mul`. The other hypotheses (`hD`, `hD'`, `hDf`) are used in the nonzero case, so only `hf` can be dropped.


## Formal Frontier (11 flagged)

### [`GradedRing.Veronese.adjoin_component_one_eq_top`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseDegreeOne.lean#L80-L104) — `formal-frontier-0005`

Snippet: `samples/formal-frontier/formal-frontier-0005.lean`

- `(hn : 0 < n)` (theorem): The statement is still true at n = 0. VeroneseRing 𝒮 0 = ⨁ j, 𝒮 (0*j). The element zeroVariable 𝒮 = of 1 (zeroUnit 𝒮 1) lies in component 𝒮 0 1. By aeval_zeroVariable_surjective (GradedRings/VeroneseZero.lean, no hypotheses on n, hgen or nontriviality), Polynomial.aeval (zeroVariable 𝒮) from (component 𝒮 0 0)[X] onto VeroneseRing 𝒮 0 is surjective. So Algebra.adjoin (component 𝒮 0 0) {zeroVariable 𝒮} = ⊤, and since {zeroVariable 𝒮} ⊆ component 𝒮 0 1, the adjoin of component 𝒮 0 1 is also ⊤. A trivial S is covered too, because the surjectivity argument is unconditional. The proof changes by splitting on n = 0 versus n > 0 (Nat.eq_zero_or_pos). The n = 0 case uses the surjectivity above via Algebra.adjoin_le and the range of aeval. The n > 0 case keeps the existing proof, where hn is only a local fact used by eval_mem_adjoin and inclusion_injective. hgen is still needed, since at n = 1 the statement is equivalent to it.

### [`Nat.DivisionGrowth.affine_lower_bound`](https://github.com/FormalFrontier/sequence-growth/blob/7b7db3df8a043a09d037de4ff1eced6873404fb2/SequenceGrowth/Data/Nat/DivisionGrowth.lean#L68-L94) — `formal-frontier-0117`

Snippet: `samples/formal-frontier/formal-frontier-0117.lean`

- `(hs : 0 < s)` (theorem): The statement stays true for s = 0 with hsn : 0 < n kept. In ℕ, `u m / 0 = 0`, so hstep is trivial. In ℚ, `(n:ℚ)/0 = 0`. Also `((0-1:ℕ):ℚ) = 0`, so offset = n*0/(n-0) = 0. The conclusion becomes `0^m * (u 0 - 0) + 0 ≤ u m`. For m = 0 this is `u 0 ≤ u 0`. For m > 0 it is `0 ≤ u m`, which holds because u m is a natural number. The proof would split on s = 0, using `simp` and `Nat.cast_nonneg` in that case, and use the existing argument when s > 0 (`Nat.pos_of_ne_zero`). The other hypothesis hsn is needed. For example s = n = 3, u 0 = 5, u 1 = 3 satisfies hstep for m = 0 but violates the conclusion. Only hs can be dropped.

### [`IsKrasner.adjoin_rootSet_le_adjoin_rootSet_of_norm_coeff_sub_lt`](https://github.com/FormalFrontier/polynomial-root-stability/blob/ceae7822f6151ec6626678db1653054d3398cff3/PolynomialRootStability/Krasner.lean#L363-L391) — `formal-frontier-0152`

Snippet: `samples/formal-frontier/formal-frontier-0152.lean`

- `(hε : 0 < ε)` (theorem): hε is implied by hcoeff. Taking i = 0 gives ‖g.coeff 0 - f.coeff 0‖ < ε, and the norm is nonnegative, so 0 < ε. The theorem therefore stays true without hε. The proof only uses hε as an argument to Mathlib's `exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`. Replace it there with `(norm_nonneg _).trans_lt (hcoeff 0)`, or add `have hε : 0 < ε := lt_of_le_of_lt (norm_nonneg _) (hcoeff 0)` at the start of the proof. No other part of the statement depends on hε.

### [`Subgroup.exists_continuous_coset_representative`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ContinuousCosetRepresentative.lean#L55-L74) — `formal-frontier-0160`

Snippet: `samples/formal-frontier/formal-frontier-0160.lean`

- `[T2Space G]` (variable): The other variable hypotheses already imply T2Space G by instance inference. (1) `TotallyDisconnectedSpace.t1Space` (Mathlib/Topology/Separation/Connected.lean:22) gives `T1Space G` from `[TotallyDisconnectedSpace G]`. (2) `T1Space.t0Space` gives `T0Space G`. (3) `IsTopologicalGroup.regularSpace` (Mathlib/Topology/Algebra/Group/Pointwise.lean:385) gives `RegularSpace G` from `[IsTopologicalGroup G]`. (4) `instT3Space` (T0 + Regular) gives `T3Space G`. (5) `T3Space.t25Space` and `T25Space.t2Space` give `T2Space G`. That Pointwise file is public-imported through `Mathlib.Topology.Algebra.Group.Quotient`, which `ContinuousSection` public-imports, so the instances are visible in this file. The statement `∃ s : C(G ⧸ H, G), ∀ q, QuotientGroup.mk (s q) = q` only needs `TopologicalSpace G`, not T2. The proof calls `quotientMapOfLE_exists_continuous_section_of_isClosed`, which requires `[T2Space G]`, and instance search will supply it from the derivation above. So the binder can be deleted (for example with `omit [T2Space G] in`) and the proof stays unchanged. The `[IsClosed ...]` instance and the other hypotheses (`CompactSpace`, `TotallyDisconnectedSpace`, `IsTopologicalGroup`) are not affected.

### [`FundamentalGroup.existsUnique_hom_of_isOpenCover`](https://github.com/FormalFrontier/fundamental-groupoids/blob/2fdb99858e3feb7a6a06ae10915f286364de2cc1/FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean#L404-L527) — `formal-frontier-0164`

Snippet: `samples/formal-frontier/formal-frontier-0164.lean`

- `(hU : IsPathConnected (U : Set X))` (theorem): hU appears only in the proof, through `leftArrow`, `leftArrow_unit` and `globalArrow_*`. The statement never mentions it, and it only concerns π₁ at p ∈ U ⊓ V. It can be dropped because U ⊓ V is path-connected (hI) and contains p. Let X' be the path component of p in X. Take a path γ from p. By the Lebesgue number lemma, γ splits into finitely many pieces, each lying in U or in V. Adjacent pieces of different type meet at a point of U ⊓ V, and merging same-type neighbours means every breakpoint lies in U ⊓ V. Each piece is a path in U (or V) with endpoints in U ⊓ V. Those endpoints lie in the path component U_p (resp. V_p) of p, because U ⊓ V is path-connected and contains p. Hence X' ⊆ U_p ∪ V_p. Also U ∩ X' = U_p, since any point of V_p ∩ U lies in U ⊓ V ⊆ U_p. Likewise V ∩ X' = V_p, and U_p ∩ V_p = U ⊓ V. So X' is covered by the open subsets U_p and V_p of X'. These are path-connected, and so is their intersection. The standard van Kampen theorem applies to X', with π₁(X',p) = π₁(X,p), π₁(U_p,p) = π₁(U,p) and π₁(V_p,p) = π₁(V,p). The same argument works if only hU is removed and hV is kept. A proof would reduce to the path component of p, or redo the open-cover argument with the arrows `leftArrow` etc. built only for the component of p. The ∃! statement stays true. hcover and hI are still needed, since without them the statement is false (for example, the circle covered by two arcs).
- `(hV : IsPathConnected (V : Set X))` (theorem): hV is symmetric to hU. It is used only in the proof, through `rightArrow`, `rightArrow_unit` and `globalArrow_*`, and does not occur in the statement. With hI (U ⊓ V path-connected, containing p) and hcover, every path in X from p decomposes into pieces in U or V with breakpoints in U ⊓ V. So the path component X' of p in X is contained in U_p ∪ V_p, with U ∩ X' = U_p, V ∩ X' = V_p and U_p ∩ V_p = U ⊓ V. Here U_p and V_p are the path components of p in U and V, and they are open in X'. Van Kampen for X' with this path-connected open cover gives the unique factorisation, and the π₁ groups at p of X', U_p, V_p equal those of X, U, V. So the ∃! statement holds without hV, whether or not hU is kept. Only the proof needs reworking, by reducing to the path component. Removing hU and hV together also works, by the same argument.

### [`GradedRing.Veronese.finiteType_of_finiteType`](https://github.com/FormalFrontier/graded-rings/blob/05143eb425d31ab18c726dc431b2314834ab8094/GradedRings/VeroneseFiniteType.lean#L105-L126) — `formal-frontier-0179`

Snippet: `samples/formal-frontier/formal-frontier-0179.lean`

- `(hn : 0 < n)` (theorem): The statement stays true for n = 0, so hn can be deleted. The conclusion only needs `Algebra.FiniteType (component 𝒮 n 0) (VeroneseRing 𝒮 n)`. Neither the algebra instance nor the ring structure uses `hn`. `VeroneseRing 𝒮 n` is `⨁ j, 𝒮 (n*j)`, and `component 𝒮 n 0` is the image of `of _ 0`. For n = 0, `VeroneseRing 𝒮 0 = ⨁ j : ℕ, 𝒮 (0*j)`, where every summand is 𝒮 0, with the multiplication induced by that of S. This is a polynomial-type ring over `component 𝒮 0 0`. It is generated as an algebra over `component 𝒮 0 0` by the single element t = `of _ 1 ⟨1, _⟩`, where 1 ∈ 𝒮 (0*1) because 0*1 reduces to 0. For any a ∈ 𝒮 (0*j), we have `of j a = of 0 ⟨a, _⟩ * t^j`, since t^j = `of j 1` and products of homogeneous summands multiply their underlying elements of S. Hence `Algebra.adjoin (component 𝒮 0 0) {t} = ⊤` by direct-sum induction. Therefore `Algebra.FiniteType` holds, as the algebra is generated by a finite set.

The current proof uses `hn` only through `finiteType_of_finite_homogeneous_generators`, whose proof needs `zeroRingEquiv` and `inclusion_injective`, which require 0 < n. So the proof must change. The n = 0 case needs this separate short argument, and the case split `n = 0` or `0 < n` replaces `hn`. The `Algebra.FiniteType (𝒮 0) S` instance is not needed for the n = 0 case.

### [`AlgebraicGeometry.Proj.degreeScaledChartMap_preimage_basicOpen`](https://github.com/FormalFrontier/projective-space/blob/3d39919aac0def769a0ff8b44e62a1317d4c84fe/ProjectiveSpace/DegreeScaledMap.lean#L453-L469) — `formal-frontier-0188`

Snippet: `samples/formal-frontier/formal-frontier-0188.lean`

- `(hn : 0 < n)` (theorem): The theorem body only uses hn to pass it to degreeScaledChartSpec_preimage_basicOpen. That lemma needs it only because Mathlib's Proj.awayι_preimage_basicOpen takes a positive-degree hypothesis hm'. The statement does not need it, and the n = 0 case reduces to the positive case.

Take a := (i.2 : A). It lies in 𝒜 i.1 with i.1 ≥ 1. Then r*a ∈ 𝒜 (n + i.1) by SetLike.mul_mem_graded, and 0 < n + i.1. So the existing lemma, applied to r*a, gives the statement for r*a.

- Left side: the chart map ends in awayι 𝒜 a, whose range is basicOpen 𝒜 a (opensRange_awayι). So its preimage of basicOpen 𝒜 r equals its preimage of basicOpen 𝒜 r ⊓ basicOpen 𝒜 a = basicOpen 𝒜 (r*a), by basicOpen_mul.
- Right side: the target is (basicOpen ℬ (f a)).ι, whose range lies in basicOpen ℬ (f a). So the preimage of basicOpen ℬ (f r) equals the preimage of basicOpen ℬ (f (r*a)), since map_mul gives f (r*a) = f r * f a.
- The case r*a thus gives the case r, and the hypotheses hd and hdeg are untouched.

The statement is also true directly in degree 0: both sides say that the homogeneous prime does not contain r (respectively f r). No junk-value issue arises, because i.1 : PNat keeps the chart degree positive. The other hypotheses stay: hd and hdeg are used by the positivity and membership proofs in the statement (Nat.mul_pos hd i.1.2, hdeg i.1 ...), and hr is needed so that r is homogeneous.

### [`finiteGroupPresentation_iff_compact_totallyDisconnected`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/FiniteGroupCharacterization.lean#L198-L214) — `formal-frontier-0200`

Snippet: `samples/formal-frontier/formal-frontier-0200.lean`

- `[T2Space G]` (theorem): T2Space G follows from IsTopologicalGroup G together with TotallyDisconnectedSpace G, so it can be deleted. The statement does not need it to elaborate: FiniteGroupPresentation G needs only Group and TopologicalSpace, and CompactSpace and TotallyDisconnectedSpace need no separation axiom. The forward direction never uses it, because it only transports compactness and total disconnectedness along the homeomorphism P.equiv. The backward direction used it only for `ProfiniteGrp.of G`. After deleting the binder, derive it from the other hypotheses. Total disconnectedness gives connectedComponent (1:G) = {1} (`connectedComponent_eq_singleton`), and `isClosed_connectedComponent` makes this set closed, so `{1}` is closed. Then `IsTopologicalGroup.t2Space_iff_one_closed` (Mathlib/Topology/Algebra/Group/Pointwise.lean) gives T2Space G. Alternatively, use `IsTopologicalGroup.t1Space G h` and the fact that topological groups are regular, `IsTopologicalGroup.regularSpace`. With `have : T2Space G := ...` in scope, the existing `ProfiniteGrp.of G` call and the rest of the proof go through unchanged.

### [`AlgebraicGeometry.Scheme.Hom.ker_radical_of_isReduced_source`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L154-L160) — `formal-frontier-0232`

Snippet: `samples/formal-frontier/formal-frontier-0232.lean`

- `[QuasiCompact f]` (theorem): The statement only needs `Scheme.Hom.ker`, which is defined without quasi-compactness as `ofIdeals fun U ↦ RingHom.ker (f.app U).hom`, the largest ideal sheaf contained in the componentwise kernel (Mathlib/AlgebraicGeometry/IdealSheaf/Basic.lean:691). Only the lemma `Hom.ker_apply` used in the proof needs `QuasiCompact`. The statement stays true without it, by a different proof. `f.ker ≤ f.ker.radical` is `le_radical`. For the converse, use `le_ofIdeals_iff : I ≤ ofIdeals J ↔ I.ideal ≤ J` with `I = f.ker.radical`. We need `∀ U, (f.ker.radical).ideal U ≤ RingHom.ker (f.app U).hom`. Take `s` in `Ideal.radical (f.ker.ideal U)`. Then `s^n ∈ f.ker.ideal U ≤ RingHom.ker (f.app U).hom` by `Hom.ideal_ker_le`. So `(f.app U s)^n = 0` in `Γ(X, f⁻¹ᵁ U)`. This ring is reduced because `X` is reduced, so `f.app U s = 0`. The degenerate case of empty `X` is covered: the target ring is trivial, and `ker_eq_top_of_isEmpty` gives `f.ker = ⊤`, whose radical is `⊤`.

### [`AlgebraicGeometry.iInf_ker_eq_vanishingIdeal_iSup_closure_range`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Scheme/JointlySchemeTheoreticallyDominant.lean#L176-L185) — `formal-frontier-0233`

Snippet: `samples/formal-frontier/formal-frontier-0233.lean`

- `[∀ j, QuasiCompact (f j)]` (theorem): The statement stays true without quasi-compactness. By `rw [vanishingIdeal_iSup]` the claim reduces to the per-index identity (f j).ker = vanishingIdeal (closure (range (f j))). That identity holds for any morphism f : X ⟶ Y with X reduced, for these reasons.

1. By definition (Mathlib `Hom.ker`), f.ker = ofIdeals (fun U ↦ RingHom.ker (f.app U)). By `le_ofIdeals_iff`, an ideal sheaf I satisfies I ≤ f.ker iff I.ideal U ≤ ker(f.app U) for every affine open U. This needs no quasi-compactness. QuasiCompact is used only in `Hom.ker_apply` and `Hom.support_ker`, which compute f.ker.ideal U exactly, and the argument below does not need either.

2. Write Z = closure(range f). `vanishingIdeal Z` has ideal U = vanishingIdeal (fromSpec ⁻¹' Z) in Γ(Y,U).

3. vanishingIdeal Z ≤ f.ker. Let s ∈ Γ(Y,U) vanish at every point of U ∩ Z. Then s vanishes at f(x) for every x ∈ f⁻¹U, so f.app U s vanishes at every point of f⁻¹U, because κ(f x) → κ(x) is a map of fields. Since X is reduced, f.app U s = 0. So vanishingIdeal Z ≤ f.ker by step 1.

4. f.ker ≤ vanishingIdeal Z. Let s ∈ f.ker.ideal U ≤ ker(f.app U) (`Hom.ideal_ker_le`, which needs no quasi-compactness). The same residue-field argument shows s vanishes on range f ∩ U. The vanishing locus of s in U is closed in U, so s also vanishes on closure(range f ∩ U), which contains Z ∩ U because U is open. So s ∈ (vanishingIdeal Z).ideal U.

The degenerate cases (empty J, empty range) are consistent: the ker is ⊤ for an empty source, and vanishingIdeal ⊥ = ⊤. The proof therefore needs a re-proof of `Hom.ker_eq_vanishingIdeal_closure_range` (and `ker_radical_of_isReduced_source`) along steps 1–4 without the QuasiCompact instance. The final `iInf` step stays as written. `[∀ j, IsReduced (X j)]` is not removable: for non-reduced sources the kernel need not be radical.

### [`MvPowerSeries.existsUnique_firstVariable_division_of_scalar_top`](https://github.com/FormalFrontier/formal-power-series/blob/9bb57357300e4fad20d074ee4cd95e8317a34c81/FormalPowerSeries/MvPowerSeries/IdealAdicRestricted/FirstVariableDivision.lean#L112-L132) — `formal-frontier-0285`

Snippet: `samples/formal-frontier/formal-frontier-0285.lean`

- `(ha : a ≠ 0)` (theorem): The statement mentions `ha` nowhere, and the proof only passes it to `existsUnique_firstVariable_division_of_leadingExponent`, which passes it on to `exists_restricted_primitive_division`. It is not needed for the truth of the statement. If `a = 0`, then `hrad` says `(span {0}).radical = ⊥ = maximalIdeal V`. In the domain `V` the radical of `⊥` is `⊥`, so the local ring `V` has zero maximal ideal and is a field `k`. Then `ham` holds trivially, and `I = span {0} = ⊥` has `I^0 = ⊤` and `I^k = ⊥` for `k ≥ 1`. So `adicallyRestrictedSubring` is exactly the finitely supported series, i.e. `MvPolynomial (Fin (n+1)) k`. Likewise for `Fin n`, and `polynomialRestrictedFinFirst` is the usual embedding `Polynomial (MvPolynomial (Fin n) k) → MvPolynomial (Fin (n+1)) k`. The residue `restrictedResidue` is `f` itself, up to the identification `k ⧸ ⊥ ≅ k`. The hypotheses `hdegree`, `htop` and `hc` then say that, viewed in `(k[X₁..Xₙ])[X₀]`, `f` has degree `d` and a leading coefficient that is a nonzero constant, hence a unit. Division with remainder by a polynomial with unit leading coefficient exists and is unique, with remainder of degree `< d`. In Mathlib this is `Polynomial.divModByMonic` after scaling by `c⁻¹`, and the uniqueness lemmas for `/ₘ` and `%ₘ`. This covers `d = 0`, where `f` is a unit and the remainder is `0` (degree `⊥ < 0`), and `n = 0`. So the conclusion holds for `a = 0`. A proof without `ha` would split on `a = 0`: the case `a ≠ 0` is the current proof, and the case `a = 0` uses the field/polynomial division argument above. I did not check the Lean details of the `a = 0` case, so the claim rests on this mathematical argument. The other hypotheses are not redundant: `[IsDomain V]` is required by `ValuationRing V`, and `hc` is needed to exclude `c = 0` with `f = 0`.

