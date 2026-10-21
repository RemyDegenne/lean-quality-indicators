# duplicates-mathlib-inclusive: run `main`, judge `claude-sonnet-5-5-high`

| Library | Sampled | Judged | Flagged | `duplicate` | `special_case` | `proof_uses_it` | Rate | 95% CI | Cost |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Mathlib | 1000 | 1000 | 263 | 37 | 226 | 150 | 26.3% | 23.7%–29.1% | $30.36 |
| Tau Ceti | 1000 | 1000 | 35 | 0 | 35 | 28 | 3.5% | 2.5%–4.8% | $20.80 |
| Lean Pool | 1000 | 1000 | 58 | 6 | 52 | 23 | 5.8% | 4.5%–7.4% | $17.79 |
| FLT (Anthropic) | 1000 | 1000 | 118 | 17 | 101 | 45 | 11.8% | 9.9%–13.9% | $30.27 |
| Formal Frontier | 1000 | 1000 | 45 | 2 | 43 | 29 | 4.5% | 3.4%–6.0% | $25.75 |

A flag is the judge's claim, not a verified fact: audit the list below. `none_found` means the judge found nothing it could justify.

## Mathlib (263 flagged)

### [`WithZeroTopology.singleton_mem_nhds_of_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/WithZeroTopology.lean#L99-L101) — `mathlib-0001`

Snippet: `samples/mathlib/mathlib-0001.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WithZeroTopology.nhds_of_ne_zero
- **file**: Mathlib/Topology/Algebra/WithZeroTopology.lean
- **derivation**: by rw [nhds_of_ne_zero h]; simp
- **proof_uses_it**: True
- **explanation**: nhds_of_ne_zero says 𝓝 γ = pure γ for γ ≠ 0 in the same file. The goal {γ} ∈ 𝓝 γ then becomes {γ} ∈ pure γ, which simp closes with mem_pure and rfl. The current proof `simp [h]` presumably already uses nhds_of_ne_zero as a simp lemma. It is not a restatement of that lemma, so this is a special case and not a duplicate. I found no more general lemma elsewhere.

### [`one_div_le_one_div_of_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Field/Basic.lean#L69-L70) — `mathlib-0005`

Snippet: `samples/mathlib/mathlib-0005.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: inv_anti₀
- **file**: Mathlib/Algebra/Order/GroupWithZero/Basic.lean
- **derivation**: simpa using inv_anti₀ ha h
- **proof_uses_it**: True
- **explanation**: inv_anti₀ (hb : 0 < b) (hba : b ≤ a) : a⁻¹ ≤ b⁻¹ is the same statement with inverses in place of 1 / _. The theorem follows by rewriting one_div, which is the one-line simpa that the current proof uses. Another declaration with this exact 1 / _ form was not found. The grep for other 1/b ≤ 1/a lemmas turned up only the target's own uses and the negative variant one_div_le_one_div_of_neg_of_le.

### [`Set.subset_sUnion_of_mem`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Set/Lattice/Bounded.lean#L186-L187) — `mathlib-0006`

Snippet: `samples/mathlib/mathlib-0006.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: le_sSup
- **file**: Mathlib/Order/CompleteLattice/Defs.lean
- **derivation**: le_sSup tS
- **proof_uses_it**: True
- **explanation**: `le_sSup : a ∈ s → a ≤ sSup s` in a complete semilattice/lattice. For `Set α`, `sSup S = ⋃₀ S` and `≤` is `⊆` (definitionally), so the theorem is `le_sSup` at the complete lattice `Set α`. The current proof is exactly `le_sSup tS`. I found no other declaration in Mathlib, Batteries or core with this statement.

### [`TensorProduct.AlgebraTensorModule.lTensor_tmul`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/TensorProduct/Tower.lean#L246-L248) — `mathlib-0010`

Snippet: `samples/mathlib/mathlib-0010.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.lTensor_tmul
- **file**: Mathlib/LinearAlgebra/TensorProduct/Map.lean
- **derivation**: LinearMap.lTensor_tmul (M := M) f m n   -- or: by simpa using LinearMap.lTensor_tmul (M := M) f m n
- **explanation**: The theorem says that the heterobasic `AlgebraTensorModule.lTensor A M f` sends `m ⊗ₜ n` to `m ⊗ₜ f n`. Mathlib's `LinearMap.lTensor_tmul` (Map.lean:353) says `f.lTensor M (m ⊗ₜ n) = m ⊗ₜ f n` for an R-linear `f`. The two maps have the same underlying function: `AlgebraTensorModule.coe_lTensor` (line 239 of the same file) is proved by `rfl`, and the theorem's own proof is `rfl`. So the target is `LinearMap.lTensor_tmul` with `lTensor A M f` read through its coercion, which is `coe_lTensor`. I did not find another declaration with the heterobasic `lTensor` on the left-hand side, so I rate it a special case and not an exact duplicate. I did not check that the `simpa` form elaborates as written. Other `lTensor_tmul` hits (`Analysis/InnerProductSpace/TensorProduct.lean`, `LinearEquiv.lTensor_tmul`) concern different maps.

### [`continuousAt_hom_bundle`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Hom.lean#L296-L302) — `mathlib-0011`

Snippet: `samples/mathlib/mathlib-0011.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FiberBundle.continuousAt_totalSpace
- **file**: Mathlib/Topology/FiberBundle/Basic.lean
- **derivation**: FiberBundle.continuousAt_totalSpace ..
- **proof_uses_it**: True
- **explanation**: FiberBundle.continuousAt_totalSpace states that for any fiber bundle, ContinuousAt f x₀ ↔ the projection is continuous at x₀ and the second component of the trivializationAt-coordinates of f x is continuous at x₀. Take the bundle to be the Hom bundle E₁ →SL[σ] E₂. Its trivializationAt unfolds definitionally to the inCoordinates expression in the statement. The current proof is exactly that single application, closed by defeq.

### [`MonoidHom.map_iterate_frobeniusEquiv_symm`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/Perfect.lean#L247-L257) — `mathlib-0012`

Snippet: `samples/mathlib/mathlib-0012.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Function.Semiconj.iterate_right
- **file**: Mathlib/Logic/Function/Iterate.lean
- **derivation**: exact (Function.Semiconj.iterate_right (MonoidHom.map_frobeniusEquiv_symm p f) n) x
- **explanation**: I found no Mathlib declaration that states this exact result. The only close ones are RingHom.map_iterate_frobeniusEquiv_symm (the ring-hom version, which is proved from the target) and MonoidHom.map_frobeniusEquiv_symm (the n = 1 case). The target is the iterated form of MonoidHom.map_frobeniusEquiv_symm. That lemma says `f ∘ (frobeniusEquiv R p).symm = (frobeniusEquiv S p).symm ∘ f`, which is `Function.Semiconj f ga gb` unfolded. `Function.Semiconj.iterate_right` (`Semiconj f ga gb → Semiconj f ga^[n] gb^[n]`) then gives the iterated statement directly, so the library's long proof via Frobenius iterates is unnecessary. The derivation uses two declarations: `Function.Semiconj.iterate_right`, and `MonoidHom.map_frobeniusEquiv_symm`, which is proved independently of the target.

### [`MeasureTheory.Measure.integral_toReal_rnDeriv`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean#L387-L389) — `mathlib-0014`

Snippet: `samples/mathlib/mathlib-0014.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.Measure.setIntegral_toReal_rnDeriv
- **file**: Mathlib/MeasureTheory/Measure/Decomposition/RadonNikodym.lean
- **derivation**: rw [← setIntegral_univ, setIntegral_toReal_rnDeriv hμν Set.univ]
- **proof_uses_it**: True
- **explanation**: The target is the case s = Set.univ of `setIntegral_toReal_rnDeriv`, which has the same hypotheses (SigmaFinite μ, SigmaFinite ν, μ ≪ ν) and states ∫ x in s, (μ.rnDeriv ν x).toReal ∂ν = μ.real s. The only glue is `setIntegral_univ`, which removes the restriction to univ. This is also the target's own proof. Alternatively, `integral_toReal_rnDeriv_mul` (which is `integral_rnDeriv_smul`) with f = 1 gives the same result via `simpa`.

### [`EuclideanSpace.volume_closedBall_fin_three`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean#L409-L412) — `mathlib-0017`

Snippet: `samples/mathlib/mathlib-0017.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: InnerProductSpace.volume_closedBall_of_dim_odd
- **file**: Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean
- **derivation**: norm_num [InnerProductSpace.volume_closedBall_of_dim_odd (k := 1) (by simp) x]
- **explanation**: `InnerProductSpace.volume_closedBall_of_dim_odd` gives the volume of a closed ball in any real finite-dimensional inner product space E with finrank = 2k+1 as `.ofReal r ^ finrank * .ofReal (π^k * 2^(k+1) / (finrank)‼)`. Take E = EuclideanSpace ℝ (Fin 3) and k = 1. Then finrank = 3, and `π * 2^2 / 3!!` simplifies to `π * 4 / 3`. The sibling `volume_ball_fin_three` is proved the same way from the ball version, `volume_ball_of_dim_odd`, using `norm_num [... (k := 1) (by simp) x]`. The target's own proof instead goes through `volume_ball_fin_three` and `addHaar_closedBall_eq_addHaar_ball`. I did not check this derivation by compiling it. It mirrors the ball proof but has not been run. I found no other declaration with this exact statement.

### [`Set.pairwise_disjoint_Ioo_intCast`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Interval/Set/Group.lean#L232-L234) — `mathlib-0020`

Snippet: `samples/mathlib/mathlib-0020.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.pairwise_disjoint_Ioo_add_intCast
- **file**: Mathlib/Algebra/Order/Interval/Set/Group.lean
- **derivation**: simpa only [zero_add] using Set.pairwise_disjoint_Ioo_add_intCast (0 : α)
- **proof_uses_it**: True
- **explanation**: `Set.pairwise_disjoint_Ioo_add_intCast (a : α)` says `Pairwise (Disjoint on fun n : ℤ => Ioo (a + n) (a + n + 1))` in the same ordered-ring setting. The target is the case a = 0, after `zero_add`. This is a distinct declaration, proved from `pairwise_disjoint_Ioo_add_zsmul`, so it does not depend on the target. A search of the Mathlib sources found no other statement of this lemma.

### [`Filter.Tendsto.ennrpow_const`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean#L487-L489) — `mathlib-0022`

Snippet: `samples/mathlib/mathlib-0022.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ENNReal.continuous_rpow_const
- **file**: Mathlib/Analysis/SpecialFunctions/Pow/Continuity.lean
- **derivation**: (ENNReal.continuous_rpow_const.tendsto a).comp hm
- **proof_uses_it**: True
- **explanation**: ENNReal.continuous_rpow_const states that a ↦ a ^ y is continuous on ℝ≥0∞ for any real y. The target is that continuity at a, composed with hm, which is `Continuous.tendsto` followed by `Tendsto.comp`. That is a one-line derivation and it is the existing proof. I found no separate Mathlib lemma with the Tendsto form for ℝ≥0∞. The nearby `Tendsto.rpow_const` at line 240 is stated for ℝ, not ℝ≥0∞.

### [`AntitoneOn.image_uIcc_subset`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Interval/Set/UnorderedInterval.lean#L187-L188) — `mathlib-0024`

Snippet: `samples/mathlib/mathlib-0024.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AntitoneOn.mapsTo_uIcc
- **file**: Mathlib/Order/Interval/Set/UnorderedInterval.lean
- **derivation**: hf.mapsTo_uIcc.image_subset
- **proof_uses_it**: True
- **explanation**: AntitoneOn.mapsTo_uIcc (line 173) states MapsTo f (uIcc a b) (uIcc (f a) (f b)) under the same hypothesis. The target is that statement rephrased with Set.MapsTo.image_subset, which turns MapsTo into f '' s ⊆ t. The existing proof is exactly this one-line derivation. This is a rephrasing rather than an instantiation of arguments, so I did not call it a full duplicate. Antitone.image_uIcc_subset has the same conclusion but needs global antitonicity, so it does not apply to the AntitoneOn setting. Grepping Mathlib for other declarations with the shape `f '' uIcc a b ⊆ uIcc …` found nothing else.

### [`ext_chart_model_space_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean#L869-L870) — `mathlib-0028`

Snippet: `samples/mathlib/mathlib-0028.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: extChartAt_model_space_eq_id
- **file**: Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.lean
- **derivation**: by rw [extChartAt_model_space_eq_id]; rfl
- **explanation**: extChartAt_model_space_eq_id (just above, line 866) states extChartAt 𝓘(𝕜, E) x = PartialEquiv.refl E. Applying both sides to y gives the target, because PartialEquiv.refl E y = y. The current proof is just rfl. extChartAt_self_apply (extChartAt I x y = I y), taken with I = 𝓘(𝕜, E), is another route. The target is a one-line corollary of these lemmas, so I count it as a special case.

### [`LeftOrdContinuous.map_sSup'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/OrdContinuous.lean#L123-L126) — `mathlib-0029`

Snippet: `samples/mathlib/mathlib-0029.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LeftOrdContinuous.map_csSup
- **file**: Mathlib/Order/OrdContinuous.lean
- **derivation**: hf.map_csSup hs (OrderTop.bddAbove s)
- **explanation**: `LeftOrdContinuous.map_csSup` states the same equation `f (sSup s) = sSup (f '' s)` for left-order-continuous `f` between `ConditionallyCompleteLattice`s, assuming `s` is nonempty and bounded above. A `CompleteLattice` is a `ConditionallyCompleteLattice` via an instance, and the `sSup` agrees definitionally. Every set in a complete lattice is bounded above, by `OrderTop.bddAbove s`, so the extra hypothesis is free. The proof of `map_csSup` uses `isLUB_csSup` and `IsLUB.csSup_eq`, not `map_sSup'`, so it is independent. The other matches I found were different: `GaloisConnection.l_sSup_eq_sSup_image` needs a Galois connection, `IsNormal.map_sSup` needs conditionally complete linear orders, and `sSupHomClass.map_sSup` has no nonempty hypothesis.

### [`Real.hasDerivAt_cosh`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean#L352-L353) — `mathlib-0031`

Snippet: `samples/mathlib/mathlib-0031.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.hasStrictDerivAt_cosh
- **file**: Mathlib/Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean
- **derivation**: (Real.hasStrictDerivAt_cosh x).hasDerivAt
- **explanation**: Real.hasStrictDerivAt_cosh (line 349) states HasStrictDerivAt cosh (sinh x) x for real x. It is a distinct declaration and its proof does not depend on the target. The target follows from it by HasStrictDerivAt.hasDerivAt, which is a one-line step. The current proof instead applies Complex.hasDerivAt_cosh and then real_of_complex. I grepped Mathlib for hasDerivAt_cosh, deriv_cosh and hasStrictDerivAt_cosh. All real-valued hits are in this same file, and none states the target other than this strict version.

### [`Ideal.pow_eq_bot`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/Ideal/Operations.lean#L401-L402) — `mathlib-0034`

Snippet: `samples/mathlib/mathlib-0034.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Submodule.pow_eq_bot
- **file**: Mathlib/Algebra/Algebra/Operations.lean
- **derivation**: Submodule.pow_eq_bot hn
- **proof_uses_it**: True
- **explanation**: Submodule.pow_eq_bot states M ^ n = ⊥ ↔ M = ⊥ for a submodule M of a reduced semiring A over R, with n ≠ 0. Ideal R is Submodule R R, so the Ideal statement is this one with A = R. The library's proof is exactly this term. Submodule.pow_eq_bot is proved directly with eq_zero_of_pow_eq_zero and aesop, so it does not depend on Ideal.pow_eq_bot.

### [`Monotone.map_iInf_of_continuousAt`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Order/Monotone.lean#L363-L367) — `mathlib-0035`

Snippet: `samples/mathlib/mathlib-0035.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Monotone.map_sInf_of_continuousAt
- **file**: Mathlib/Topology/Order/Monotone.lean
- **derivation**: by rw [iInf, Mf.map_sInf_of_continuousAt Cf ftop, ← range_comp]; rfl
- **explanation**: Monotone.map_sInf_of_continuousAt has the same hypotheses (continuity at the infimum, monotone, f ⊤ = ⊤) and concludes f (sInf s) = sInf (f '' s). The indexed version is the instance s = range g. iInf g unfolds to sInf (range g), and range_comp turns f '' range g into range (f ∘ g). I found no other statement of this result: the only other indexed variants are Monotone.map_ciInf_of_continuousAt and Antitone.map_iInf_of_continuousAt, which have different hypotheses. The derivation is not entirely trivial: it unfolds iInf and rewrites with range_comp. The current proof instead dualizes Monotone.map_iSup_of_continuousAt. That lemma is proved in the same file by the same kind of rewrite chain from map_sSup_of_continuousAt.

### [`ContinuousLinearMap.coe_domRestrict`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Restrict.lean#L103-L105) — `mathlib-0046`

Snippet: `samples/mathlib/mathlib-0046.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.coe_domRestrict
- **file**: Mathlib/Algebra/Module/Submodule/LinearMap.lean
- **derivation**: LinearMap.coe_domRestrict f.toLinearMap p
- **explanation**: LinearMap.coe_domRestrict (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : ⇑(f.domRestrict p) = Set.domRestrict p f is the same statement for plain semilinear maps. Applying it to f.toLinearMap gives the continuous version up to definitional unfolding. ContinuousLinearMap.domRestrict is f ∘SL p.subtypeL, and its toLinearMap is f.toLinearMap.domRestrict p (this is toLinearMap_domRestrict, proved by rfl). The current proof is just `rfl`. I found no other Mathlib lemma that states the continuous-linear coercion equality directly.

### [`Subring.coe_natCast`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Ring/Subring/Defs.lean#L393-L394) — `mathlib-0047`

Snippet: `samples/mathlib/mathlib-0047.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SubringClass.coe_natCast
- **file**: Mathlib/Algebra/Ring/Subring/Defs.lean
- **derivation**: exact SubringClass.coe_natCast s n
- **explanation**: SubringClass.coe_natCast (line 152) states ((n : s) : R) = n for any s : S with [SetLike S R] [SubringClass S R], over a NonAssocRing R. It's proved by rfl and tagged simp, norm_cast. Taking S := Subring R gives the target statement. The target's own proof is also rfl and doesn't cite the class lemma. The two NatCast instances on ↥s are defeq, so the lemma applies directly. It is a special case rather than a pure duplicate because S has to be instantiated to Subring R.

### [`measurableAtom_subset`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean#L310-L312) — `mathlib-0048`

Snippet: `samples/mathlib/mathlib-0048.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: mem_of_mem_measurableAtom
- **file**: Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean
- **derivation**: fun _ h => mem_of_mem_measurableAtom h hs hx
- **explanation**: `mem_of_mem_measurableAtom` (line 305) states: if y ∈ measurableAtom x, s is measurable and x ∈ s, then y ∈ s. `measurableAtom_subset` says measurableAtom x ⊆ s for measurable s with x ∈ s. Unfolding `⊆` gives the same statement as `∀ y, y ∈ measurableAtom x → y ∈ s`, with the arguments in a different order. The existing proof does not use `mem_of_mem_measurableAtom`; it uses `iInter₂_subset_of_subset`. The candidate's proof is independent: it only unfolds the definition and applies `mem_iInter`. It does not depend on the target.

### [`BialgHom.coe_fn_inj`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/Bialgebra/Hom.lean#L191-L192) — `mathlib-0051`

Snippet: `samples/mathlib/mathlib-0051.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: DFunLike.coe_fn_eq
- **file**: Mathlib/Basic/FunLike/Basic.lean
- **derivation**: DFunLike.coe_fn_eq
- **proof_uses_it**: True
- **explanation**: DFunLike.coe_fn_eq states, for any F with a DFunLike instance, that (f : ∀ a, β a) = g ↔ f = g. BialgHom has a FunLike instance, so the target is that statement with F := A →ₐc[R] B. This is the exact statement, and the existing proof is that one-term application. The target is only a BialgHom-specific restatement of the generic lemma.

### [`NNReal.one_le_rpow`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean#L369-L370) — `mathlib-0053`

Snippet: `samples/mathlib/mathlib-0053.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.one_le_rpow
- **file**: Mathlib/Analysis/SpecialFunctions/Pow/Real.lean
- **derivation**: Real.one_le_rpow h h₁
- **proof_uses_it**: True
- **explanation**: Real.one_le_rpow says that 1 ≤ x and 0 ≤ z give 1 ≤ x ^ z for real x and z. The NNReal statement is the same fact for x : ℝ≥0, where the order and the rpow are the real ones through the coercion. The current proof is the single term `Real.one_le_rpow h h₁`. It is not a strict duplicate, because the statement is about ℝ≥0 and Mathlib's is about ℝ, so I classed it as a special case. The only other candidate, the ENNReal `one_le_rpow` in the same file, is a different statement: it needs 0 < z and is about ℝ≥0∞.

### [`mul_inv`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/Basic.lean#L522-L523) — `mathlib-0057`

Snippet: `samples/mathlib/mathlib-0057.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Commute.mul_inv
- **file**: Mathlib/Algebra/Group/Commute/Defs.lean
- **derivation**: exact (Commute.all a b).mul_inv
- **explanation**: Commute.mul_inv states (a * b)⁻¹ = a⁻¹ * b⁻¹ for commuting a, b in a DivisionMonoid. In a DivisionCommMonoid every pair commutes, so instantiating hab := Commute.all a b gives the theorem. Its proof is `rw [hab.eq, mul_inv_rev]`, so it does not depend on the target. The duplicates in ENNReal and EReal are for specific types and so are only special cases going the other way.

### [`Matroid.IsColoop.mem_of_isBase`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Combinatorics/Matroid/Loop.lean#L548-L549) — `mathlib-0059`

Snippet: `samples/mathlib/mathlib-0059.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Matroid.IsBase.mem_of_isColoop
- **file**: Mathlib/Combinatorics/Matroid/Loop.lean
- **derivation**: fun he hB => hB.mem_of_isColoop he
- **explanation**: `Matroid.IsBase.mem_of_isColoop` (line 545) states `(hB : M.IsBase B) (he : M.IsColoop e) : e ∈ B`. This is the target with its two hypotheses in the opposite order. Its proof goes through `isColoop_iff_forall_mem_isBase`, not through the target, so it is independent. The target's own proof uses the same iff lemma instead of calling it.

### [`inner_re_zero_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/InnerProductSpace/Basic.lean#L199-L200) — `mathlib-0061`

Snippet: `samples/mathlib/mathlib-0061.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: inner_zero_right
- **file**: Mathlib/Analysis/InnerProductSpace/Defs.lean
- **derivation**: by rw [inner_zero_right, map_zero]
- **proof_uses_it**: True
- **explanation**: I found no separate Mathlib lemma stating `re ⟪x, 0⟫ = 0`. The statement is `inner_zero_right` (`⟪x, 0⟫ = 0`, in Defs.lean at line 263) with `re` applied to both sides. It follows by rewriting with `inner_zero_right` and then `map_zero` (`re 0 = 0`). The library's proof does exactly this, and `by simp` also works. I grepped Mathlib for `re_zero_right`, `re_inner_zero` and `inner_zero_right` and found nothing closer.

### [`MeasureTheory.AEStronglyMeasurable.real_toNNReal`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean#L540-L543) — `mathlib-0062`

Snippet: `samples/mathlib/mathlib-0062.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Continuous.comp_aestronglyMeasurable
- **file**: Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean
- **derivation**: continuous_real_toNNReal.comp_aestronglyMeasurable hf
- **proof_uses_it**: True
- **explanation**: Continuous.comp_aestronglyMeasurable says that a continuous g composed with an AEStronglyMeasurable f is AEStronglyMeasurable. Taking g = Real.toNNReal, which is continuous by continuous_real_toNNReal, gives the theorem. The current proof is exactly this one-liner. I read the usage sites but not the declaration of Continuous.comp_aestronglyMeasurable itself. The analogous StronglyMeasurable.real_toNNReal is a separate declaration in Basic.lean for a different predicate, so it is not a match.

### [`LinearIndependent.of_subsingleton`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/LinearIndependent/Defs.lean#L892-L893) — `mathlib-0063`

Snippet: `samples/mathlib/mathlib-0063.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearIndependent.of_subsingleton'
- **file**: Mathlib/LinearAlgebra/LinearIndependent/Defs.lean
- **derivation**: .of_subsingleton' i (by simp [hi])
- **proof_uses_it**: True
- **explanation**: The target is a corollary of the sibling lemma `LinearIndependent.of_subsingleton'`, in the same file just above it. That lemma has the same conclusion for any ring `R`, with the hypothesis `∀ r, r • v i = 0 → r = 0`. Under `IsDomain R` and `IsTorsionFree R M`, that hypothesis follows from `v i ≠ 0` by `simp [hi]`. This is also exactly the current proof. I also checked `linearIndependent_unique_iff` and `linearIndependent_subsingleton_index_iff` in `LinearIndependent/Basic.lean`. Both are circular: the first is proved using the target, and the second is proved from the first. I found no other independent Mathlib declaration with this statement.

### [`Representation.IntertwiningMap.rTensor_smul`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RepresentationTheory/Intertwining.lean#L764-L766) — `mathlib-0068`

Snippet: `samples/mathlib/mathlib-0068.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Representation.IntertwiningMap.tensor_smul_left
- **file**: Mathlib/RepresentationTheory/Intertwining.lean
- **derivation**: tensor_smul_left _ _ _
- **proof_uses_it**: True
- **explanation**: `rTensor ρ f` is defined as `tensor f (id ρ)`. `tensor_smul_left a f g : (a • f).tensor g = a • (f.tensor g)` is a distinct declaration with an independent proof (`ext; simp [TensorProduct.smul_tmul]`). Taking `g := id ρ` gives `rTensor_smul` after unfolding `rTensor`. The current proof is exactly this one-line instantiation. I searched only Mathlib/RepresentationTheory and found no other candidate.

### [`ContinuousAffineEquiv.refl_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/ContinuousAffineEquiv.lean#L151-L153) — `mathlib-0071`

Snippet: `samples/mathlib/mathlib-0071.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContinuousAffineEquiv.coe_refl
- **file**: Mathlib/Topology/Algebra/ContinuousAffineEquiv.lean
- **derivation**: congrFun coe_refl x
- **explanation**: `coe_refl : ⇑(refl k P₁) = id` is a distinct declaration in the same file. `refl_apply` is its pointwise form, so `congrFun coe_refl x` proves it, because `id x` unfolds to `x`. Both lemmas are proved by `rfl` from the definition of `refl`. I found no other lemma elsewhere in Mathlib that states this, so the match rests on `coe_refl`, and it is a weak one: the step from `coe_refl` is only `congrFun`.

### [`Dvd.dvd.modEq_zero_int`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Int/ModEq.lean#L100-L101) — `mathlib-0079`

Snippet: `samples/mathlib/mathlib-0079.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Int.modEq_zero_iff_dvd
- **file**: Mathlib/Data/Int/ModEq.lean
- **derivation**: modEq_zero_iff_dvd.2 h
- **proof_uses_it**: True
- **explanation**: `Int.modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a` is a separate declaration, at line 97 of the same file. The target theorem is its `.mpr` direction, restated as a dot-notation lemma on `Dvd.dvd`. The current proof is exactly `modEq_zero_iff_dvd.2 h`. I did not search for other candidates.

### [`Subgroup.relIndex_comap_ne_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/GroupTheory/Index.lean#L390-L396) — `mathlib-0092`

Snippet: `samples/mathlib/mathlib-0092.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Subgroup.IsFiniteRelIndex.comap
- **file**: Mathlib/GroupTheory/Index.lean
- **derivation**: exact (IsFiniteRelIndex.comap f ⟨hJK⟩).relIndex_ne_zero
- **explanation**: `IsFiniteRelIndex H K` is a Prop class whose only field is `H.relIndex K ≠ 0` (see `isFiniteRelIndex_iff_relIndex_ne_zero`). `Subgroup.IsFiniteRelIndex.comap` (line 874) states that `IsFiniteRelIndex H K` implies `IsFiniteRelIndex (H.comap f) (K.comap f)`. Unfolding the class gives the target lemma exactly. Its proof uses `isFiniteRelIndex_comap_iff`, `map_comap_eq` and `isFiniteRelIndex_of_le_right`, not the target, so it is independent. It sits later in the same file (line 874 against 393) and `relIndex_comap_ne_zero` is only used earlier, in `relIndex_inter_ne_zero`.

### [`Set.image_div_const_Ioc`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Group/Pointwise/Interval.lean#L448-L450) — `mathlib-0093`

Snippet: `samples/mathlib/mathlib-0093.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: OrderIso.image_Ioc
- **file**: Mathlib/Order/Interval/Set/OrderIso.lean
- **derivation**: exact (OrderIso.divRight a).image_Ioc b c
- **explanation**: OrderIso.image_Ioc (e : α ≃o β) (a b : α) : e '' Ioc a b = Ioc (e a) (e b). Instantiating e := OrderIso.divRight a (the order iso x ↦ x / a, defined in Mathlib/Algebra/Order/Group/OrderIso.lean for a group with MulRightMono) gives the target statement. The coercion of divRight a is definitionally fun x => x / a, and divRight a b is definitionally b / a, so the exact term should typecheck by defeq; if not, `simpa using` with the simps lemma OrderIso.divRight_apply is the fallback. The library's own proof is `simp [div_eq_mul_inv]` and does not use this lemma. Not tested, since Lean can't be run here.

### [`Finset.union_empty`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Finset/Lattice/Lemmas.lean#L50-L52) — `mathlib-0105`

Snippet: `samples/mathlib/mathlib-0105.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sup_bot_eq
- **file**: Mathlib/Order/BoundedOrder/Lattice.lean
- **derivation**: exact sup_bot_eq s
- **explanation**: Finset has a Lattice instance (Mathlib/Data/Finset/Lattice/Basic.lean:67) whose ⊔ is ∪, and an OrderBot instance (Mathlib/Data/Finset/Empty.lean:173) whose ⊥ is ∅ (`Finset.bot_eq_empty`). The generic lemma `sup_bot_eq : a ⊔ ⊥ = a` instantiated at `Finset α` gives `s ∪ ∅ = s` up to definitional unfolding. If `exact` does not unify, use `by simpa using sup_bot_eq s` or `(sup_bot_eq s : s ⊔ ⊥ = s)`. I did not open the file that declares `sup_bot_eq`; its path above is from memory. The generic lemma is independent of `Finset.union_empty`.

### [`Unitization.cobounded_eq_aux`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Algebra/Unitization.lean#L195-L198) — `mathlib-0113`

Snippet: `samples/mathlib/mathlib-0113.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: bornology_eq_of_bilipschitz
- **file**: Mathlib/Topology/MetricSpace/Bilipschitz.lean
- **derivation**: bornology_eq_of_bilipschitz antilipschitzWith_addEquiv lipschitzWith_addEquiv
- **explanation**: `bornology_eq_of_bilipschitz` states `@cobounded _ (induced f) = cobounded α` for `f` Lipschitz and antilipschitz between pseudo-metric spaces. The theorem is the case `f = addEquiv 𝕜 A : Unitization 𝕜 A → 𝕜 × A`, using the local auxiliary normed-ring instance on `Unitization`. The current proof is the body of that lemma, `le_antisymm lipschitzWith_addEquiv.comap_cobounded_le antilipschitzWith_addEquiv.tendsto_cobounded.le_comap`, with the same two hypotheses. I did not check that `Unitization.lean` imports `Bilipschitz.lean`. The Bilipschitz lemma's proof does not depend on the Unitization file.

### [`CategoryTheory.NatIso.unop_whiskerRight`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Opposites.lean#L697-L701) — `mathlib-0115`

Snippet: `samples/mathlib/mathlib-0115.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.NatTrans.unop_whiskerRight
- **file**: Mathlib/CategoryTheory/Opposites.lean
- **derivation**: Iso.ext (NatTrans.unop_whiskerRight α.hom)
- **explanation**: The isomorphism statement is the same as the NatTrans version at line 447 of the same file, applied to α.hom. The NatTrans version says NatTrans.unop (whiskerRight α H) = (unopComp).hom ≫ whiskerRight (NatTrans.unop α) H.unop ≫ (unopComp).inv. The Iso version follows by `Iso.ext`, since the hom components of NatIso.unop, isoWhiskerRight and Iso.trans unfold definitionally to those terms. I did not check that the term elaborates, so it might need `by ext; simpa using ...` instead. The only other hits for `unop_whiskerRight` were the monoidal-category lemma on morphisms and the sibling `unop_whiskerLeft`, and neither matches.

### [`MeasureTheory.projectiveFamilyContent_mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean#L134-L137) — `mathlib-0116`

Snippet: `samples/mathlib/mathlib-0116.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.addContent_mono
- **file**: Mathlib/MeasureTheory/Measure/AddContent.lean
- **derivation**: addContent_mono isSetSemiring_measurableCylinders hs ht hst
- **proof_uses_it**: True
- **explanation**: `addContent_mono` states that for an additive content m on a set semiring C, s, t ∈ C and s ⊆ t give m s ≤ m t. The target is this statement with C = measurableCylinders α and m = projectiveFamilyContent hP. The semiring hypothesis comes from `isSetSemiring_measurableCylinders`. The existing proof is exactly this one-line application.

### [`affineSegment_vadd_const_image`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Convex/Between.lean#L65-L68) — `mathlib-0120`

Snippet: `samples/mathlib/mathlib-0120.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: affineSegment_image
- **file**: Mathlib/Analysis/Convex/Between.lean
- **derivation**: affineSegment_image (AffineEquiv.vaddConst R p : V →ᵃ[R] P) x y
- **proof_uses_it**: True
- **explanation**: The general lemma `affineSegment_image (f : P →ᵃ[R] P') (x y : P) : f '' affineSegment R x y = affineSegment R (f x) (f y)` is a distinct declaration. The target is that lemma applied to the affine equivalence `AffineEquiv.vaddConst R p`, which acts as `· +ᵥ p`. This is exactly the current proof, a single application. I did not find a more general or independent statement elsewhere in Mathlib.

### [`Inseparable.specializes'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Inseparable.lean#L462-L462) — `mathlib-0124`

Snippet: `samples/mathlib/mathlib-0124.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: inseparable_iff_specializes_and
- **file**: Mathlib/Topology/Inseparable.lean
- **derivation**: (inseparable_iff_specializes_and.mp h).2
- **explanation**: `inseparable_iff_specializes_and : (x ~ᵢ y) ↔ x ⤳ y ∧ y ⤳ x` is a distinct declaration, proved by `le_antisymm_iff`, so it does not depend on the target. Its second component is exactly `y ⤳ x`. The current proof is `h.ge`, which uses the specialization preorder directly. Another derivation is `h.symm.specializes` from `Inseparable.specializes`, which sits right next to the target. I did not read the source of `Inseparable.symm`.

### [`CategoryTheory.MonoidalClosed.curry_eq`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean#L197-L198) — `mathlib-0129`

Snippet: `samples/mathlib/mathlib-0129.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Adjunction.homEquiv_unit
- **file**: Mathlib/CategoryTheory/Adjunction/Basic.lean
- **derivation**: (ihom.adjunction A).homEquiv_unit
- **explanation**: `curry` is defined as `(ihom.adjunction A).homEquiv _ _`, and `ihom.coev A` is defined as `(ihom.adjunction A).unit`. `Adjunction.homEquiv_unit` (an alias of the simps lemma `homEquiv_apply`) says `adj.homEquiv X Y f = adj.unit.app X ≫ G.map f`. Instantiating it with `adj := ihom.adjunction A`, `F := tensorLeft A` and `G := ihom A` gives `curry_eq`, and the two sides agree by unfolding definitions. The current proof is `rfl`, so it doesn't use this lemma. I haven't checked how the elaborator unifies `curry g` with `homEquiv ... g` in the derivation. I read the statements of these declarations but did not compile the derivation.

### [`LieSubmodule.normalizer_inf`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Lie/Normalizer.lean#L68-L69) — `mathlib-0132`

Snippet: `samples/mathlib/mathlib-0132.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: GaloisConnection.u_inf
- **file**: Mathlib/Order/GaloisConnection/Basic.lean
- **derivation**: exact LieSubmodule.gc_top_lie_normalizer.u_inf
- **explanation**: The theorem is `LieSubmodule.normalizer_inf`. `LieSubmodule.gc_top_lie_normalizer` (Normalizer.lean:87) is a Galois connection whose upper adjoint is `normalizer`. Its proof is `top_lie_le_iff_le_normalizer`, which does not use `normalizer_inf`. `GaloisConnection.u_inf` is the dual of `l_sup`, which is stated at line 89 of the Galois connection file. It says that an upper adjoint preserves binary infima: `u (b₁ ⊓ b₂) = u b₁ ⊓ u b₂`. Instantiating it with `u := normalizer` gives the statement, and the lattice of Lie submodules supplies the semilattice instances. I did not find any other Lie-algebra lemma stating the same thing. I read the `u_inf` usage at line 281 and the `l_sup` statement, but did not read the generated `u_inf` declaration itself. Since it is generated by `to_dual`, I have not confirmed its exact name or signature.

### [`List.cons_head?_tail`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/List/Basic.lean#L440-L444) — `mathlib-0142`

Snippet: `samples/mathlib/mathlib-0142.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: List.eq_cons_of_mem_head?
- **file**: Mathlib/Data/List/Basic.lean
- **derivation**: fun h => (eq_cons_of_mem_head? h).symm
- **explanation**: `List.eq_cons_of_mem_head?` (Mathlib/Data/List/Basic.lean:414) says `x ∈ l.head? → l = x :: tail l`. The target says `a ∈ head? l → a :: tail l = l`. These are the same statement with the equation sides swapped. The existing proof of `eq_cons_of_mem_head?` is direct and does not use `cons_head?_tail`, so the match is independent. I found nothing in core or Batteries with this statement.

### [`LinearMap.rank_le_range`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Dimension/LinearMap.lean#L43-L44) — `mathlib-0147`

Snippet: `samples/mathlib/mathlib-0147.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.rank_le
- **file**: Mathlib/LinearAlgebra/Dimension/Basic.lean
- **derivation**: Submodule.rank_le _
- **proof_uses_it**: True
- **explanation**: `LinearMap.rank f` unfolds to `Module.rank K (LinearMap.range f)`. The theorem is therefore `Submodule.rank_le` applied to the submodule `range f` of `V'`: `Module.rank K ↥s ≤ Module.rank K M` for `s : Submodule K M`. The current proof is exactly `Submodule.rank_le _`. The only step is unfolding the definition `LinearMap.rank`.

### [`Convex.norm_image_sub_le_of_norm_fderiv_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/MeanValue.lean#L498-L504) — `mathlib-0148`

Snippet: `samples/mathlib/mathlib-0148.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
- **file**: Mathlib/Analysis/Calculus/MeanValue.lean
- **derivation**: hs.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) bound xs ys
- **proof_uses_it**: True
- **explanation**: Mathlib's `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` has the same conclusion ‖f y - f x‖ ≤ C * ‖y - x‖ for an arbitrary derivative family f' with HasFDerivWithinAt f (f' x) s x and ‖f' x‖ ≤ C. The target is the case f' = fderiv 𝕜 f. Differentiability at x gives HasFDerivAt, which gives HasFDerivWithinAt. That is the current proof, so the target is a thin wrapper of that lemma. A second route is `Convex.norm_image_sub_le_of_norm_fderiv_le'` with φ = 0. I found no other declaration with this statement; the `fderivWithin`, `Lipschitz` and `deriv` variants have different hypotheses or conclusions.

### [`CentroidHom.toEnd_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Ring/CentroidHom.lean#L131-L132) — `mathlib-0156`

Snippet: `samples/mathlib/mathlib-0156.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CentroidHom.coe_toAddMonoidHom_injective
- **file**: Mathlib/Algebra/Ring/CentroidHom.lean
- **derivation**: coe_toAddMonoidHom_injective
- **proof_uses_it**: True
- **explanation**: `CentroidHom.toEnd f` is defined as `(f : α →+ α)`, and `AddMonoid.End α` is definitionally `α →+ α`. So `toEnd_injective` is `coe_toAddMonoidHom_injective` after unfolding `toEnd`. The current proof already uses it directly. The two statements differ only by that unfolding. I only searched the same file and did not look for a separate Mathlib declaration.

### [`Nat.mem_smoothNumbers_of_primeFactors_subset`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/NumberTheory/SmoothNumbers.lean#L287-L290) — `mathlib-0158`

Snippet: `samples/mathlib/mathlib-0158.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.mem_factoredNumbers_of_primeFactors_subset
- **file**: Mathlib/NumberTheory/SmoothNumbers.lean
- **derivation**: rw [smoothNumbers_eq_factoredNumbers]; exact mem_factoredNumbers_of_primeFactors_subset hm hp
- **proof_uses_it**: True
- **explanation**: `Nat.mem_factoredNumbers_of_primeFactors_subset` (line 98) states that `m ≠ 0` and `m.primeFactors ⊆ s` give `m ∈ factoredNumbers s`. The target is that statement with `s = Finset.range n`. The only extra step is rewriting with `smoothNumbers_eq_factoredNumbers`, which says `smoothNumbers n = factoredNumbers (Finset.range n)`. The current proof is already exactly this one-line instantiation. I found no other declaration in Mathlib, Batteries or Lean core that states the result directly. `mem_smoothNumbers_iff_primeFactors_subset` is the nearest candidate, but its proof calls the target, so it is circular and doesn't count.

### [`Real.enorm_ofReal_of_nonneg`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Group/Real.lean#L100-L101) — `mathlib-0160`

Snippet: `samples/mathlib/mathlib-0160.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.enorm_eq_ofReal
- **file**: Mathlib/Analysis/Normed/Group/Real.lean
- **derivation**: by rw [enorm_eq_self]; exact (Real.enorm_eq_ofReal ha).symm
- **explanation**: The enorm on ℝ≥0∞ is the identity (`enorm_eq_self`, rfl), so the goal is `ENNReal.ofReal a = ‖a‖ₑ`. That is `Real.enorm_eq_ofReal ha` (`‖r‖ₑ = .ofReal r` for 0 ≤ r) with the sides swapped. The current proof uses the sibling lemma `Real.enorm_of_nonneg`, which has the same statement as `Real.enorm_eq_ofReal`. The proof of `Real.enorm_eq_ofReal` goes through `ofReal_norm` and does not depend on the target.

### [`groupHomology.d₂₁_single_self_inv_ρ_sub_inv_self`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RepresentationTheory/Homological/GroupHomology/LowDegree.lean#L168-L173) — `mathlib-0161`

Snippet: `samples/mathlib/mathlib-0161.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: groupHomology.d₂₁_single_inv_self_ρ_sub_self_inv
- **file**: Mathlib/RepresentationTheory/Homological/GroupHomology/LowDegree.lean
- **derivation**: by simpa only [inv_inv] using d₂₁_single_inv_self_ρ_sub_self_inv g⁻¹ a
- **explanation**: The sibling lemma at line 161 states d₂₁ A (single (g⁻¹, g) (ρ g⁻¹ a) - single (g, g⁻¹) a) = single 1 a - single 1 (ρ g⁻¹ a). Substituting g := g⁻¹ and simplifying g⁻¹⁻¹ = g with inv_inv gives exactly the target statement. Its proof is independent: it uses d₂₁_single, self_inv_apply and abel, not the target. I did not run this derivation. It could need `simpa using` instead of `simpa only [inv_inv]`.

### [`SeparationQuotient.surjective_mk`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Inseparable.lean#L593-L594) — `mathlib-0165`

Snippet: `samples/mathlib/mathlib-0165.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Quot.mk_surjective
- **file**: Mathlib/Data/Quot.lean
- **derivation**: Quot.mk_surjective
- **proof_uses_it**: True
- **explanation**: SeparationQuotient.mk is by definition Quot.mk of the Inseparable relation (SeparationQuotient X is a Quot/Quotient of the setoid). Quot.mk_surjective says Quot.mk r is surjective for any relation r. The target is that statement with r instantiated to Inseparable, after unfolding mk. The current proof is exactly this term.

### [`MulOpposite.nndist_unop`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean#L100-L101) — `mathlib-0167`

Snippet: `samples/mathlib/mathlib-0167.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MulOpposite.nndist_op
- **file**: Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean
- **derivation**: (nndist_op (unop x) (unop y)).symm
- **explanation**: The only other candidate is the sibling lemma `MulOpposite.nndist_op (x y : α) : nndist (op x) (op y) = nndist x y`, two lines below the target in the same file. Instantiating it at `unop x` and `unop y` gives `nndist (op (unop x)) (op (unop y)) = nndist (unop x) (unop y)`. Its `.symm` has the target's type up to the defeq `op (unop x) = x`, which holds by structure eta. Both lemmas are proved by `rfl`, so neither depends on the other. The current proof is `rfl`, not this derivation. I grepped Mathlib for `nndist_unop`, `nndist_op` and related spellings. The only hits were these two lemmas. I did not try the derivation in Lean.

### [`Real.geom_mean_le_arith_mean4_weighted`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/MeanInequalities.lean#L402-L408) — `mathlib-0168`

Snippet: `samples/mathlib/mathlib-0168.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: NNReal.geom_mean_le_arith_mean4_weighted
- **file**: Mathlib/Analysis/MeanInequalities.lean
- **derivation**: NNReal.geom_mean_le_arith_mean4_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨w₃, hw₃⟩ ⟨w₄, hw₄⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ ⟨p₃, hp₃⟩ ⟨p₄, hp₄⟩ (NNReal.coe_inj.1 hw)
- **proof_uses_it**: True
- **explanation**: The NNReal statement (line 378) is the same four-term weighted AM-GM inequality for ℝ≥0 weights and points, with coerced exponents. The Real version applies it to the subtype elements ⟨wᵢ, hwᵢ⟩ and ⟨pᵢ, hpᵢ⟩, and turns the sum hypothesis into an NNReal equation with NNReal.coe_inj. The library's own proof is exactly this single term. This is a transfer from ℝ≥0 to ℝ rather than a match with an independent Mathlib proof. A more general declaration, Real.geom_mean_le_arith_mean_weighted over a Finset, would need a Fin-sum simp, which is longer than two lines. I did not find a Real four-term statement outside this file.

### [`Submodule.norm_sq_eq_add_norm_sq_starProjection`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean#L607-L610) — `mathlib-0170`

Snippet: `samples/mathlib/mathlib-0170.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Submodule.norm_sq_eq_add_norm_sq_projection
- **file**: Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean
- **derivation**: norm_sq_eq_add_norm_sq_projection x S
- **proof_uses_it**: True
- **explanation**: `Submodule.norm_sq_eq_add_norm_sq_projection` (line 597 of the same file) states ‖x‖^2 = ‖S.orthogonalProjectionOnto x‖^2 + ‖Sᗮ.orthogonalProjectionOnto x‖^2, with the same hypotheses. `starProjection x` is the coercion of `orthogonalProjectionOnto x` into E, and the norm on a submodule is the norm of the coerced element. So the two statements are the same result, and the target's proof is the one-line term `norm_sq_eq_add_norm_sq_projection x S`. The target is a restatement in terms of `starProjection`.

### [`SSet.δ_opObjEquiv`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicTopology/SimplicialSet/Op.lean#L72-L74) — `mathlib-0174`

Snippet: `samples/mathlib/mathlib-0174.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SSet.op_δ
- **file**: Mathlib/AlgebraicTopology/SimplicialSet/Op.lean
- **derivation**: by rw [op_δ]; simp
- **proof_uses_it**: True
- **explanation**: The only candidate is `SSet.op_δ` in the same file: `X.op.δ i x = opObjEquiv.symm (X.δ i.rev (opObjEquiv x))`. It is a distinct declaration and is proved from `SimplicialObject.δ` and `op_map`, not from the target. The target is the same fact solved for `X.δ`. Rewriting `op_δ` at `X.op.δ i.rev x` leaves `opObjEquiv (opObjEquiv.symm (X.δ i.rev.rev (opObjEquiv x)))`, and `simp` closes that using `Fin.rev_rev` and `Equiv.apply_symm_apply`. The target's own proof is `simp`, which uses `op_δ` because it is a simp lemma. Grepping Mathlib for `opObjEquiv` and for `δ` together with `opObjEquiv` found no other declaration with this content; the other hits only use the target.

### [`Multiset.mem_Ici`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Interval/Multiset.lean#L82-L82) — `mathlib-0183`

Snippet: `samples/mathlib/mathlib-0183.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.mem_Ici
- **file**: Mathlib/Order/Interval/Finset/Defs.lean
- **derivation**: by rw [Ici, ← Finset.mem_def, Finset.mem_Ici]
- **proof_uses_it**: True
- **explanation**: Multiset.Ici a is defined as (Finset.Ici a).val, so membership in it is membership in Finset.Ici a (Finset.mem_def). Finset.mem_Ici states x ∈ Finset.Ici a ↔ a ≤ x. Multiset.mem_Ici is that lemma after unfolding the definition, and the current proof already does exactly that. Nothing else in Mathlib states it for Multiset.Ici, which is defined in the same file.

### [`MeasureTheory.VectorMeasure.ennrealVariation_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/VectorMeasure/Variation/Basic.lean#L60-L62) — `mathlib-0192`

Snippet: `samples/mathlib/mathlib-0192.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.VectorMeasure.Measure.toENNRealVectorMeasure_apply_measurable
- **file**: Mathlib/MeasureTheory/VectorMeasure/Operations.lean
- **derivation**: Measure.toENNRealVectorMeasure_apply_measurable hs
- **proof_uses_it**: True
- **explanation**: `ennrealVariation μ` is defined as `μ.variation.toENNRealVectorMeasure`. The target statement is therefore `Measure.toENNRealVectorMeasure_apply_measurable` with the measure instantiated to `μ.variation`. The lemma says `ν.toENNRealVectorMeasure i = ν i` for measurable `i`. The existing proof is exactly that term, after unfolding the definition. I searched the other `ennrealVariation` lemmas in the repo and found no other declaration stating this. The name and namespace of the matched lemma are taken from the grep hit, so I did not check them separately. The lemma sits in `Operations.lean` at line 115, in the `MeasureTheory` namespace (the file's namespace was not checked).

### [`AddChar.sum_ne_zero_iff_eq_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/AddChar.lean#L345-L345) — `mathlib-0193`

Snippet: `samples/mathlib/mathlib-0193.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddChar.sum_eq_zero_iff_ne_zero
- **file**: Mathlib/Algebra/Group/AddChar.lean
- **derivation**: sum_eq_zero_iff_ne_zero.not_left
- **proof_uses_it**: True
- **explanation**: The theorem is the negated-left form of AddChar.sum_eq_zero_iff_ne_zero (∑ ψ x = 0 ↔ ψ ≠ 0), which is a distinct declaration in the same file with the same hypotheses. Its proof goes through sum_eq_ite, not through the target, so it is independent. The target follows by `Iff.not_left`, and the current proof is exactly that. The statements differ only by moving a negation across the iff. I found no other Mathlib declaration, such as in LegendreSymbol/AddCharacter, that states this iff.

### [`CategoryTheory.Pretriangulated.Triangle.shiftFunctorAdd_eq`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Triangulated/TriangleShift.lean#L182-L186) — `mathlib-0199`

Snippet: `samples/mathlib/mathlib-0199.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.ShiftMkCore.shiftFunctorAdd_eq
- **file**: Mathlib/CategoryTheory/Shift/Basic.lean
- **derivation**: ShiftMkCore.shiftFunctorAdd_eq _ _ _
- **proof_uses_it**: True
- **explanation**: The `HasShift (Triangle C) ℤ` instance is built with `hasShiftMk` from a `ShiftMkCore` whose `add` field is `fun a b => Triangle.shiftFunctorAdd' C a b _ rfl`. `ShiftMkCore.shiftFunctorAdd_eq (h : ShiftMkCore C A) (a b : A)` says that, for the instance built by `hasShiftMk` from `h`, `shiftFunctorAdd C a b = h.add a b`. Taking `h` to be the Triangle core gives the target statement. The current proof is exactly this application. The target is an instance-specific API lemma. Its content is the general `hasShiftMk` unfolding lemma, and it adds nothing beyond the definition of the core. The only other lemma I found named `shiftFunctorAdd_eq` outside this file is for homotopy categories, and it is not a match.

### [`Multiset.cons_product`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Multiset/Bind.lean#L312-L313) — `mathlib-0201`

Snippet: `samples/mathlib/mathlib-0201.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Multiset.cons_bind
- **file**: Mathlib/Data/Multiset/Bind.lean
- **derivation**: by simpa [SProd.sprod, product] using Multiset.cons_bind a s (fun a => t.map (Prod.mk a))
- **explanation**: Multiset.product s t is defined as s.bind (fun a => t.map (Prod.mk a)), and `×ˢ` unfolds to it. Multiset.cons_bind says (a ::ₘ s).bind f = f a + s.bind f. Taking f := fun a => t.map (Prod.mk a) gives cons_product after unfolding the definition. This is probably true by `rfl`-style defeq as well, so `cons_bind ..` might work directly. The current proof is `simp [SProd.sprod, product]`, which reaches cons_bind via the simp set rather than citing it. I found no other Mathlib or Batteries declaration with this statement. Multiset.cons_product is the only one named cons_product. List.product_cons is the list version.

### [`ContinuousAlternatingMap.hasBasis_nhds_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/Module/Alternating/Topology.lean#L166-L170) — `mathlib-0219`

Snippet: `samples/mathlib/mathlib-0219.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContinuousAlternatingMap.hasBasis_nhds_zero_of_basis
- **file**: Mathlib/Topology/Algebra/Module/Alternating/Topology.lean
- **derivation**: hasBasis_nhds_zero_of_basis (Filter.basis_sets _)
- **proof_uses_it**: True
- **explanation**: The target is the general lemma `ContinuousAlternatingMap.hasBasis_nhds_zero_of_basis`, with the basis of `𝓝 0 : Filter F` taken to be the filter's own sets (`Filter.basis_sets`). That lemma is a distinct declaration, proved independently via `nhds_induced` and `ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis`, and it does not depend on the target. The analogous `ContinuousMultilinearMap.hasBasis_nhds_zero` is stated for a different type, so it is not a duplicate. I found no other alternating-map statement of this result.

### [`uniformContinuous_nnnorm'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Group/Uniform.lean#L193-L195) — `mathlib-0220`

Snippet: `samples/mathlib/mathlib-0220.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: lipschitzWith_one_nnnorm'
- **file**: Mathlib/Analysis/Normed/Group/Uniform.lean
- **derivation**: exact lipschitzWith_one_nnnorm'.uniformContinuous
- **explanation**: Mathlib's `lipschitzWith_one_nnnorm'` (same file, line 186) states `LipschitzWith 1 (NNNorm.nnnorm : E → ℝ≥0)`, and its proof does not use the target. `LipschitzWith.uniformContinuous` gives `UniformContinuous nnnorm`, which equals `fun a => ‖a‖₊` up to eta. The current proof goes through `uniformContinuous_norm'.subtype_mk` instead. I found no separate Mathlib lemma that states the target directly.

### [`Int.tendsto_coe_cofinite`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Instances/ZMultiples.lean#L49-L53) — `mathlib-0221`

Snippet: `samples/mathlib/mathlib-0221.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: tendsto_cofinite_cocompact_of_discrete
- **file**: Mathlib/Topology/DiscreteSubset.lean
- **derivation**: exact tendsto_cofinite_cocompact_of_discrete Int.isClosedEmbedding_coe_real.tendsto_cocompact
- **explanation**: `tendsto_cofinite_cocompact_of_discrete` says that for a discrete domain X, if f tends to cocompact along cocompact, then f tends to cocompact along cofinite. Take X = ℤ and f = (↑ : ℤ → ℝ). `Int.isClosedEmbedding_coe_real` (Mathlib/Topology/Instances/Int.lean:46) gives a closed embedding, and `IsClosedEmbedding.tendsto_cocompact` turns that into the hypothesis. The `DiscreteTopology ℤ` instance is found by instance search. The library's own proof instead goes through `MonoidHom.tendsto_coe_cofinite_of_isDiscrete` applied to `castAddHom ℝ`. I did not check how `Int.isClosedEmbedding_coe_real` is proved, but it sits in an earlier file than the target, so I don't expect it to depend on the target.

### [`CauSeq.zero_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/CauSeq/Basic.lean#L238-L240) — `mathlib-0238`

Snippet: `samples/mathlib/mathlib-0238.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CauSeq.coe_zero
- **file**: Mathlib/Algebra/Order/CauSeq/Basic.lean
- **derivation**: congr_fun coe_zero i
- **explanation**: `CauSeq.coe_zero : ⇑(0 : CauSeq β abv) = 0` is proved by `rfl`, independently of `zero_apply`. Applying it pointwise gives `(0 : CauSeq β abv) i = (0 : ℕ → β) i`. That is definitionally `0` by `Pi.zero_apply`, so `congr_fun coe_zero i` proves `zero_apply`. The two statements are the same fact, one as a function equality and one evaluated at a point. Both are `rfl` lemmas about the definition of `0` on `CauSeq`. I found no other declaration in Mathlib, Batteries or Lean core that states this.

### [`Nat.cast_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/CharZero/Defs.lean#L65-L66) — `mathlib-0241`

Snippet: `samples/mathlib/mathlib-0241.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CharZero.cast_injective
- **file**: Mathlib/Algebra/CharZero/Defs.lean
- **derivation**: CharZero.cast_injective
- **proof_uses_it**: True
- **explanation**: `Nat.cast_injective` is only a wrapper around the structure field `CharZero.cast_injective`, which is declared at line 47 of the same file. The field has the same statement, `Function.Injective (Nat.cast : ℕ → R)`, for `[AddMonoidWithOne R]` and `[CharZero R]`. It is a separate declaration, and the wrapper's proof is exactly that field. This is only a trivial alias. I found no other lemma in Mathlib with this statement, and I did not search further.

### [`intervalIntegral.integral_div`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean#L824-L827) — `mathlib-0245`

Snippet: `samples/mathlib/mathlib-0245.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: intervalIntegral.integral_mul_const
- **file**: Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean
- **derivation**: simpa only [div_eq_mul_inv] using intervalIntegral.integral_mul_const r⁻¹ f
- **proof_uses_it**: True
- **explanation**: integral_mul_const (line 820, same file) states ∫ x in a..b, f x * r ∂μ = (∫ x in a..b, f x ∂μ) * r for RCLike 𝕜. Taking r⁻¹ and rewriting division as multiplication by the inverse gives integral_div. This is the current proof. I found no other interval-integral division lemma. The Bochner version MeasureTheory.integral_div is for ∫ over a measure, not intervals. Getting from it to the interval integral would need case analysis on a ≤ b.

### [`CategoryTheory.Triangulated.TStructure.isLE_truncLE_obj`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Triangulated/TStructure/TruncLEGT.lean#L44-L46) — `mathlib-0248`

Snippet: `samples/mathlib/mathlib-0248.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Triangulated.TStructure.isLE_truncLT_obj
- **file**: Mathlib/CategoryTheory/Triangulated/TStructure/TruncLTGE.lean
- **derivation**: t.isLE_truncLT_obj X (a + 1) b
- **proof_uses_it**: True
- **explanation**: `truncLE n` is defined as `truncLT (n + 1)`. `isLE_truncLT_obj X a b (hn : a ≤ b + 1)` says `t.IsLE ((t.truncLT a).obj X) b`. Taking `a := a + 1` gives the target, and its hypothesis `a + 1 ≤ b + 1` follows from `a ≤ b` by `lia`. The current proof already applies this lemma, so the target is a thin wrapper that specializes it to `truncLE`. I found no other declaration that matches more closely.

### [`DifferentiableOn.continuousMultilinear_apply_const`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/FDeriv/CompCLM.lean#L208-L211) — `mathlib-0251`

Snippet: `samples/mathlib/mathlib-0251.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Differentiable.comp_differentiableOn
- **file**: Mathlib/Analysis/Calculus/FDeriv/Comp.lean
- **derivation**: (ContinuousMultilinearMap.apply 𝕜 M H u).differentiable.comp_differentiableOn hc
- **explanation**: The map y ↦ c y u is the composition of c with the continuous linear evaluation map ContinuousMultilinearMap.apply 𝕜 M H u (Mathlib/Topology/Algebra/Module/Multilinear/Topology.lean). Continuous linear maps are differentiable (ContinuousLinearMap.differentiable), and Differentiable.comp_differentiableOn composes that with the DifferentiableOn hypothesis hc. This is the same method the neighbouring pointwise lemmas use, with HasFDerivAt.comp. The current proof instead applies the DifferentiableWithinAt version pointwise. I did not read the signature of ContinuousMultilinearMap.apply to see whether it needs any extra instance, but the neighbouring lemmas use it without one.

### [`contDiffAt_prod`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/ContDiff/Operations.lean#L483-L486) — `mathlib-0253`

Snippet: `samples/mathlib/mathlib-0253.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: contDiffAt_prod'
- **file**: Mathlib/Analysis/Calculus/ContDiff/Operations.lean
- **derivation**: by simpa only [← Finset.prod_apply] using contDiffAt_prod' h
- **explanation**: The same file has `contDiffAt_prod'` (line 479). It has the same hypotheses and gives `ContDiffAt 𝕜 n (∏ i ∈ t, f i) x`, where the product is taken in the function (Pi) ring. The target is the pointwise form `fun y => ∏ i ∈ t, f i y`. The two functions are equal by `Finset.prod_apply`, so one `simpa only [← Finset.prod_apply]` converts between them. This is the same one-line `simpa` step that `contDiffWithinAt_prod` uses to go from its primed version. The current proof instead applies `contDiffWithinAt_prod`, the unprimed `WithinAt` version, at the set `s = univ`. That is a third declaration in the same family, and the primed `ContDiffAt` lemma is an independent route. A grep for `ContDiffAt` statements with a product turned up only these two in Mathlib, so there is no other candidate.

### [`ContinuousAffineMap.smul_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/ContinuousAffineMap.lean#L270-L270) — `mathlib-0254`

Snippet: `samples/mathlib/mathlib-0254.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContinuousAffineMap.coe_smul
- **file**: Mathlib/Topology/Algebra/ContinuousAffineMap.lean
- **derivation**: congrFun (coe_smul t f) x
- **explanation**: `ContinuousAffineMap.coe_smul` (line 268, same section and hypotheses) states `⇑(t • f) = t • ⇑f`. `smul_apply` is its pointwise form, obtained by applying both sides to `x` with `congrFun`. Both are proved by `rfl`, and `coe_smul` does not depend on `smul_apply`. The only other candidate is `AffineMap.coe_smul`, which is about non-continuous affine maps. I found no separate `smul_apply` for continuous affine maps.

### [`PartOrd.hom_ofHom`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Category/PartOrd.lean#L113-L115) — `mathlib-0255`

Snippet: `samples/mathlib/mathlib-0255.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.ConcreteCategory.hom_ofHom
- **file**: Mathlib/CategoryTheory/ConcreteCategory/Basic.lean
- **derivation**: exact ConcreteCategory.hom_ofHom (C := PartOrd) f
- **explanation**: PartOrd.ofHom is an abbrev for ConcreteCategory.ofHom (C := PartOrd) f, and PartOrd.Hom.hom is an abbrev for ConcreteCategory.hom (C := PartOrd). So the target is exactly the generic field lemma ConcreteCategory.hom_ofHom (a simp lemma, a field of the ConcreteCategory class) at C := PartOrd. The current proof is `rfl`.

### [`Bornology.isVonNBounded_singleton`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/LocallyConvex/Bounded.lean#L278-L280) — `mathlib-0259`

Snippet: `samples/mathlib/mathlib-0259.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.Finite.isVonNBounded
- **file**: Mathlib/Analysis/LocallyConvex/Bounded.lean
- **derivation**: (Set.finite_singleton x).isVonNBounded
- **explanation**: `Set.Finite.isVonNBounded` (line 290 of the same file, under the same typeclass assumptions) says any finite set in `E` is von Neumann bounded. Its proof uses `absorbs_finite` directly and doesn't depend on `isVonNBounded_singleton`. Taking `s := {x}` with `Set.finite_singleton x` gives the target. The current proof is different: it applies `absorbent_nhds_zero hV` and then `.absorbs`. I also checked `IsCompact.isVonNBounded`, which would work through `isCompact_singleton` but needs stronger assumptions (`IsTopologicalAddGroup`).

### [`add_tsub_add_le_tsub_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Sub/Defs.lean#L160-L162) — `mathlib-0260`

Snippet: `samples/mathlib/mathlib-0260.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: add_tsub_add_le_tsub_left
- **file**: Mathlib/Algebra/Order/Sub/Defs.lean
- **derivation**: by rw [add_comm a c, add_comm b c]; exact add_tsub_add_le_tsub_left
- **explanation**: The only close match is the sibling add_tsub_add_le_tsub_left (a + b - (a + c) ≤ b - c), under identical hypotheses, in the same file. Since α is an AddCommSemigroup, rewriting with add_comm turns a + c - (b + c) into c + a - (c + b), so the left version gives it. It is a commuted mirror of the target, not a different result. The equality add_tsub_add_eq_tsub_right needs extra hypotheses (AddLeftReflectLE), so it doesn't apply, and its proof uses the target. I found no other declaration that states this inequality.

### [`Filter.smul_bot`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Filter/Pointwise.lean#L838-L840) — `mathlib-0262`

Snippet: `samples/mathlib/mathlib-0262.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Filter.map₂_bot_right
- **file**: Mathlib/Order/Filter/NAry.lean
- **derivation**: map₂_bot_right
- **proof_uses_it**: True
- **explanation**: Pointwise scalar multiplication of filters is defined as `map₂ (· • ·) f g`. So `f • ⊥ = ⊥` is `map₂_bot_right` with `m := (· • ·)`, after unfolding the definition. The library's proof is exactly `map₂_bot_right`. The same lemma gives the other pointwise `*_bot` lemmas nearby (lines 320, 430, 935), so `smul_bot` is a direct instantiation of a general lemma.

### [`ProbabilityTheory.condIndep_of_condIndep_of_le_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Independence/Conditional.lean#L467-L472) — `mathlib-0264`

Snippet: `samples/mathlib/mathlib-0264.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ProbabilityTheory.Kernel.indep_of_indep_of_le_right
- **file**: Mathlib/Probability/Independence/Kernel/Indep.lean
- **derivation**: Kernel.indep_of_indep_of_le_right h_indep h32
- **proof_uses_it**: True
- **explanation**: CondIndep m' m₁ m₂ hm' μ is by definition Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm'). The theorem is Kernel.indep_of_indep_of_le_right with κ := condExpKernel μ m' and μ := μ.trim hm', after unfolding the definition. The current proof is exactly that application. I did not find a separate, non-kernel statement with the same form.

### [`Btw.btw.antisymm`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Circular.lean#L254-L255) — `mathlib-0267`

Snippet: `samples/mathlib/mathlib-0267.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CircularPartialOrder.btw_antisymm
- **file**: Mathlib/Order/Circular.lean
- **derivation**: btw_antisymm h
- **proof_uses_it**: True
- **explanation**: The class field `CircularPartialOrder.btw_antisymm {a b c : α} : btw a b c → btw c b a → a = b ∨ b = c ∨ c = a` (line 144, exported at line 146) is exactly this statement. `Btw.btw.antisymm` is only a dot-notation wrapper for it, and the file's own TODO comment says so. The field is a separate declaration, and its proof doesn't depend on the theorem.

### [`QuadraticAlgebra.discr_intCast`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean#L67-L69) — `mathlib-0269`

Snippet: `samples/mathlib/mathlib-0269.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuadraticAlgebra.discr_algebraMap
- **file**: Mathlib/Algebra/QuadraticAlgebra/Discriminant.lean
- **derivation**: by simpa using discr_algebraMap (R := ℤ) (S := R) a b
- **explanation**: `discr_algebraMap` (line 63, same file but a distinct declaration) says `discr (algebraMap R S a) (algebraMap R S b) = algebraMap R S (discr a b)` for any algebra `S` over `R`. Its proof, `simp [discr_def, map_ofNat]`, does not use `discr_intCast`. Taking `R := ℤ` and `S := R` gives the target. The step uses `algebraMap ℤ R n = (n : R)` (`eq_intCast`/`algebraMap_int_eq`), which `simp` knows. The current proof of `discr_intCast` is a direct `simp [discr_def]`. I searched for `discr_*` lemmas in Mathlib and found no other candidate. I did not run Lean, so the `simpa` derivation is untested.

### [`RootPairing.reflectionPerm_involutive`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/RootSystem/Defs.lean#L289-L290) — `mathlib-0270`

Snippet: `samples/mathlib/mathlib-0270.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: RootPairing.reflectionPerm_self
- **file**: Mathlib/LinearAlgebra/RootSystem/Defs.lean
- **derivation**: fun j => P.reflectionPerm_self i j
- **explanation**: `Function.Involutive f` is by definition `∀ x, f (f x) = x`. `RootPairing.reflectionPerm_self` (line 285, same file) states `P.reflectionPerm i (P.reflectionPerm i j) = j`, which is exactly that for `f = P.reflectionPerm i`. Its proof goes through `P.root.injective`, `root_reflectionPerm` and `reflection_same`. It does not use `reflectionPerm_involutive`, so the match is not circular. The target's own proof instead goes through `involutive_iff_iter_2_eq_id`. I found no other match: a grep for `reflectionPerm` with `involutive` or `Involutive` only turned up this file.

### [`QuadraticAlgebra.C_eq_algebraMap`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/QuadraticAlgebra/Defs.lean#L455-L456) — `mathlib-0272`

Snippet: `samples/mathlib/mathlib-0272.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuadraticAlgebra.algebraMap_eq
- **file**: Mathlib/Algebra/QuadraticAlgebra/Defs.lean
- **derivation**: funext fun r => (algebraMap_eq r).symm
- **explanation**: `QuadraticAlgebra.algebraMap_eq (r : R) : algebraMap R (QuadraticAlgebra R a b) r = .C r` (line 427, `rfl`, under the same `CommSemiring R`) is the pointwise form of the target. The target is the function-level equation `C = algebraMap R _`, which follows by `funext` and `.symm`. The current proof is `rfl`, so it doesn't use `algebraMap_eq`. I didn't search outside this file, since the match is in the same file.

### [`ContinuousLinearMap.toLinearMap_mul`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean#L570-L572) — `mathlib-0285`

Snippet: `samples/mathlib/mathlib-0285.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContinuousLinearMap.toLinearMap_comp
- **file**: Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean
- **derivation**: (toLinearMap_comp f g).trans (Module.End.mul_eq_comp _ _).symm
- **explanation**: The target says the coercion of f * g to a linear map equals f * g in Module.End. Multiplication on M₁ →L[R₁] M₁ is defined as comp (mul_def), and on Module.End it is LinearMap.comp (Module.End.mul_eq_comp). The general lemma ContinuousLinearMap.toLinearMap_comp says ↑(h ∘SL f) = ↑h ∘ₛₗ ↑f. Taking σ₁₂ = σ₂₃ = σ₁₃ = RingHom.id and M₂ = M₃ = M₁ gives the target, up to mul_eq_comp. The current proof is `rfl`, so it doesn't use that lemma. Both lemmas are themselves proved by `rfl`, so the content sits in the definitions. I found no other lemma that states this directly. The deprecated alias coe_mul is the target itself.

### [`Real.summable_one_div_nat_pow`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/PSeries.lean#L328-L332) — `mathlib-0286`

Snippet: `samples/mathlib/mathlib-0286.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Real.summable_nat_pow_inv
- **file**: Mathlib/Analysis/PSeries.lean
- **derivation**: by simpa only [one_div] using Real.summable_nat_pow_inv (p := p)
- **proof_uses_it**: True
- **explanation**: Real.summable_nat_pow_inv states Summable (fun n => ((n : ℝ) ^ p)⁻¹) ↔ 1 < p. The target is the same statement with 1 / (n:ℝ)^p in place of ((n:ℝ)^p)⁻¹. These are equal by `one_div`, which is only a change of surface form. The target's proof is `simp only [one_div, Real.summable_nat_pow_inv]`, so it already uses the other lemma. That lemma's proof goes through summable_nat_rpow_inv and does not depend on the target.

### [`BooleanSubalgebra.supClosed`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/BooleanSubalgebra.lean#L44-L44) — `mathlib-0287`

Snippet: `samples/mathlib/mathlib-0287.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Sublattice.supClosed
- **file**: Mathlib/Order/Sublattice.lean
- **derivation**: L.toSublattice.supClosed
- **explanation**: BooleanSubalgebra extends Sublattice. Mathlib has `Sublattice.supClosed (L : Sublattice α) : SupClosed (L : Set α)` (Sublattice.lean line 59). Applying it to `L.toSublattice` gives the target statement, because the coercion of a Boolean subalgebra to a set is definitionally the carrier of its underlying sublattice. The current proof uses the structure field `L.supClosed'` directly instead. I found no other match. The match is a bit weak: both lemmas just restate a structure field.

### [`indicator_le_thickenedIndicatorAux`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/MetricSpace/ThickenedIndicator.lean#L101-L106) — `mathlib-0289`

Snippet: `samples/mathlib/mathlib-0289.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.indicator_le
- **file**: Mathlib/Algebra/Order/Group/Indicator.lean
- **derivation**: Set.indicator_le fun a ha => (thickenedIndicatorAux_one δ E ha).ge
- **explanation**: Set.indicator_le (additive version of mulIndicator_le, for canonically ordered additive monoids such as ℝ≥0∞) says: if f a ≤ g a for all a ∈ s, then s.indicator f ≤ g. Take f = fun _ => 1 and g = thickenedIndicatorAux δ E. The hypothesis is exactly thickenedIndicatorAux_one, which gives the value 1 on E. So the target follows by instantiating this general lemma, with a one-line side proof. I did not find a declaration that states the target as is. I confirmed the statement of mulIndicator_le in the source. I assumed the to_additive name Set.indicator_le and did not check the generated declaration.

### [`Set.inv_mem_inv`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean#L206-L207) — `mathlib-0298`

Snippet: `samples/mathlib/mathlib-0298.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.mem_inv
- **file**: Mathlib/Algebra/Group/Pointwise/Set/Basic.lean
- **derivation**: by rw [mem_inv, inv_inv]
- **proof_uses_it**: True
- **explanation**: `Set.mem_inv : a ∈ s⁻¹ ↔ a⁻¹ ∈ s`. Instantiating it at a⁻¹ gives a⁻¹ ∈ s⁻¹ ↔ a⁻¹⁻¹ ∈ s, and `inv_inv` finishes. The current proof is `simp only [mem_inv, inv_inv]`, which already does this. I found no other declaration that states the result. The other `inv_mem_inv` lemmas I found are for Filter, Finset, Part and intervals, and they are different statements.

### [`CategoryTheory.Abelian.SpectralObject.mono_H_map_twoδ₁Toδ₀'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Homology/SpectralObject/Basic.lean#L224-L226) — `mathlib-0301`

Snippet: `samples/mathlib/mathlib-0301.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Abelian.SpectralObject.mono_H_map_twoδ₁Toδ₀
- **file**: Mathlib/Algebra/Homology/SpectralObject/Basic.lean
- **derivation**: X'.mono_H_map_twoδ₁Toδ₀ _ _ _ _ _ h₁
- **proof_uses_it**: True
- **explanation**: The target is the instance of the general lemma `mono_H_map_twoδ₁Toδ₀` (stated for arbitrary morphisms f, g, fg in a category ι) for a preorder ι', with f := homOfLE h₀₁, g := homOfLE h₁₂, fg := homOfLE _. `twoδ₁Toδ₀'` is the preorder version of `twoδ₁Toδ₀`. The existing proof is the one-line application of the general lemma. That lemma is a distinct declaration and does not depend on the target; its proof uses `exact₂`.

### [`FractionalIdeal.mul_inf`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean#L287-L288) — `mathlib-0307`

Snippet: `samples/mathlib/mathlib-0307.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: mul_inf₀
- **file**: Mathlib/Algebra/Order/GroupWithZero/OrderIso.lean
- **derivation**: mul_inf₀ (zero_le _) _ _
- **proof_uses_it**: True
- **explanation**: `mul_inf₀` states `c * (a ⊓ b) = c * a ⊓ c * b` for `0 ≤ c` in a `SemilatticeInf G₀` with `PosMulReflectLT`. `FractionalIdeal.mul_inf` is that statement with `G₀ := FractionalIdeal A⁰ K`. The hypothesis `0 ≤ c` holds by `zero_le`. This is the library's current proof, and it is a one-line instantiation.

### [`PointedCone.DualFG.dual_dual_flip`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Geometry/Convex/Cone/DualFinite.lean#L94-L99) — `mathlib-0313`

Snippet: `samples/mathlib/mathlib-0313.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PointedCone.dual_dual_flip_dual
- **file**: Mathlib/Geometry/Convex/Cone/Dual.lean
- **derivation**: obtain ⟨s, rfl⟩ := hC
exact dual_dual_flip_dual (p := p) (s : Set M)
- **proof_uses_it**: True
- **explanation**: `DualFG p C` means `C = dual p ↑s` for a finset `s`. `dual_dual_flip_dual` says `dual p (dual p.flip (dual p s)) = dual p s` for any set `s`. Taking `s := ↑s` gives the theorem directly. The current proof already uses this lemma. It first rewrites `C` as `dual p D` for a finitely generated cone `D`, which is a detour, and then applies the lemma with `D`. I found no other general statement of this form: the only other `dual_dual_flip` in Mathlib is `ProperCone.dual_dual_flip`, which is a different setting.

### [`UpperHalfPlane.IsZeroAtImInfty.valueAtInfty_eq_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/NumberTheory/ModularForms/QExpansion.lean#L76-L78) — `mathlib-0314`

Snippet: `samples/mathlib/mathlib-0314.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Filter.Tendsto.limUnder_eq
- **file**: Mathlib/Topology/Algebra/Order/LiminfLimsup.lean
- **derivation**: hf.limUnder_eq
- **proof_uses_it**: True
- **explanation**: `valueAtInfty f` is defined as `limUnder atImInfty f`, and `IsZeroAtImInfty f` is `Tendsto f atImInfty (𝓝 0)`. The lemma is `Filter.Tendsto.limUnder_eq` (in a T2 space, `Tendsto f l (𝓝 a) → limUnder l f = a`) with the filter set to `atImInfty` and the limit set to `0`. The file path for `Tendsto.limUnder_eq` is my guess and I did not grep for it. The library's own proof is already `hf.limUnder_eq`. I only searched for other uses of `valueAtInfty` and found no other lemma stating this result.

### [`Sym2.mk_fst_out_snd_out`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Sym/Sym2.lean#L365-L366) — `mathlib-0320`

Snippet: `samples/mathlib/mathlib-0320.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Quotient.out_eq
- **file**: Mathlib/Data/Quot.lean
- **derivation**: z.out_eq
- **proof_uses_it**: True
- **explanation**: Sym2 α is Quotient (Sym2.Rel.setoid α), and s(a, b) is Sym2.mk (a, b). The target statement is Quotient.out_eq (⟦q.out⟧ = q) specialised to Sym2, with `z.out` unfolded into its components by pair eta. The current proof is exactly `z.out_eq`, i.e. Quotient.out_eq. I did not find a separate Sym2-specific or more general declaration beyond that.

### [`ciInf_le_ciSup`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/ConditionallyCompleteLattice/Indexed.lean#L191-L194) — `mathlib-0323`

Snippet: `samples/mathlib/mathlib-0323.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: csInf_le_csSup
- **file**: Mathlib/Order/ConditionallyCompleteLattice/Basic.lean
- **derivation**: csInf_le_csSup (Set.range_nonempty f) hf hf'
- **explanation**: `csInf_le_csSup` says that for a nonempty set s that is bounded below and above, sInf s ≤ sSup s. Take s = range f. Then ⨅ i, f i unfolds to sInf (range f) and ⨆ i, f i unfolds to sSup (range f). The nonemptiness of range f comes from `Set.range_nonempty f`, which uses `[Nonempty ι]`. The current proof instead chains `ciInf_le` and `le_ciSup` through an arbitrary index. The only other near-match is `Directed.ciInf_le_ciSup`, which is a different statement with extra hypotheses.

### [`Polynomial.taylor_pow`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Polynomial/Taylor.lean#L150-L152) — `mathlib-0324`

Snippet: `samples/mathlib/mathlib-0324.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.pow_comp
- **file**: Mathlib/Algebra/Polynomial/Eval/Defs.lean
- **derivation**: by simpa only [taylor_apply] using pow_comp f (X + C r) n
- **explanation**: taylor r f is by definition f.comp (X + C r) (taylor_apply, rfl). pow_comp states (p ^ n).comp q = p.comp q ^ n for a commutative semiring. Instantiating q := X + C r gives the statement. The current proof uses map_pow on taylorAlgHom, a general homomorphism law.

### [`LaurentSeries.coeff_coe_powerSeries`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/LaurentSeries.lean#L223-L226) — `mathlib-0325`

Snippet: `samples/mathlib/mathlib-0325.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HahnSeries.ofPowerSeries_apply_coeff
- **file**: Mathlib/RingTheory/HahnSeries/PowerSeries.lean
- **derivation**: ofPowerSeries_apply_coeff x n
- **proof_uses_it**: True
- **explanation**: The coercion `(x : R⸨X⸩)` is `ofPowerSeries ℤ R x`. The target is `HahnSeries.ofPowerSeries_apply_coeff` with `Γ := ℤ`, which states `(ofPowerSeries Γ R x).coeff n = PowerSeries.coeff n x` for a general ordered semiring Γ. The current proof is `rw [ofPowerSeries_apply_coeff]`, so it already uses that lemma.

### [`QuotientGroup.out_eq'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/GroupTheory/Coset/Defs.lean#L203-L205) — `mathlib-0326`

Snippet: `samples/mathlib/mathlib-0326.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Quotient.out_eq'
- **file**: Mathlib/Data/Quot.lean
- **derivation**: Quotient.out_eq' a
- **proof_uses_it**: True
- **explanation**: `Quotient.out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q` is the general statement for an arbitrary setoid. `QuotientGroup.out_eq'` is the case where the setoid is the left-coset relation `QuotientGroup.leftRel s`. Here `α ⧸ s` is `Quotient (leftRel s)` and `QuotientGroup.mk` is `Quotient.mk''`, so the two agree by definitional unfolding. The current proof is already exactly `Quotient.out_eq' a`. I found no other match: `GroupTheory/DoubleCoset.lean` has an `out_eq'` for double cosets, which is a different statement.

### [`ENNReal.add_le_add_iff_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Basic/ENNReal/Operations.lean#L124-L125) — `mathlib-0329`

Snippet: `samples/mathlib/mathlib-0329.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WithTop.add_le_add_iff_right
- **file**: Mathlib/Algebra/Order/Monoid/Unbundled/WithTop.lean
- **derivation**: WithTop.add_le_add_iff_right
- **proof_uses_it**: True
- **explanation**: The general lemma states that for a type α with Add, LE, AddRightMono and AddRightReflectLE, and z ≠ ⊤ in WithTop α, x + z ≤ y + z ↔ x ≤ y. ENNReal is WithTop ℝ≥0 by definition, so the theorem is the case α = ℝ≥0. The current proof is exactly this lemma. Mathlib has no separate ENNReal statement, only that instantiation. ENat.add_le_add_iff_right is the analogous case α = ℕ.

### [`Finset.card_disjiUnion`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean#L1000-L1003) — `mathlib-0331`

Snippet: `samples/mathlib/mathlib-0331.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.sum_disjiUnion
- **file**: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
- **derivation**: by rw [card_eq_sum_ones, sum_disjiUnion]; simp
- **explanation**: The statement is the cardinality version of Finset.sum_disjiUnion (the additive form of prod_disjiUnion, line 126 of the same file). Taking f = 1 there and using card_eq_sum_ones together with sum_const_one gives the result. I did not check that the derivation compiles, so it is a sketch. The current proof uses the multiset lemma Multiset.card_bind instead. I searched for other Finset-level card lemmas: card_biUnion needs DecidableEq and pairwise disjointness, and card_sigma is about sigma, so neither is an exact duplicate.

### [`prod_mem_nhds`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Constructions/SumProd.lean#L306-L308) — `mathlib-0338`

Snippet: `samples/mathlib/mathlib-0338.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Filter.prod_mem_prod
- **file**: Mathlib/Order/Filter/Prod.lean
- **derivation**: by rw [nhds_prod_eq]; exact Filter.prod_mem_prod hx hy
- **explanation**: Filter.prod_mem_prod (hs : s ∈ f) (ht : t ∈ g) : s ×ˢ t ∈ f ×ˢ g, with f = 𝓝 x, g = 𝓝 y, together with nhds_prod_eq : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y, gives the statement in one rewrite. The library's own proof instead applies the iff prod_mem_nhds_iff (s ×ˢ t ∈ 𝓝 (x, y) ↔ s ∈ 𝓝 x ∧ t ∈ 𝓝 y), whose mpr direction is exactly this theorem. That iff is a separate declaration, so it is also a valid source.

### [`Subgroup.map_one_eq_bot`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/Subgroup/Map.lean#L150-L154) — `mathlib-0343`

Snippet: `samples/mathlib/mathlib-0343.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.map_eq_bot_iff
- **file**: Mathlib/Algebra/Group/Subgroup/Ker.lean
- **derivation**: (Subgroup.map_eq_bot_iff K).2 (by simp)
- **explanation**: `Subgroup.map_eq_bot_iff : H.map f = ⊥ ↔ H ≤ f.ker` (proved via `gc_map_comap`, independent of the target). Take f = 1. The side goal `K ≤ (1 : G →* N).ker` is closed by `simp`, using the simp lemma `MonoidHom.ker_one : (1 : G →* M).ker = ⊤` and `le_top`. The current proof instead shows `K.map 1 ≤ ⊥` directly by elements. I found no declaration stating `map 1 = ⊥` itself. `range_one` and `ker_one` are the nearest statements but are not the same result. This is a borderline case: the derivation is one lemma plus a simp side goal, but the statement is not a literal instance of the lemma.

### [`SSet.mapFundamentalGroupoid_obj_mk`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Basic.lean#L357-L359) — `mathlib-0345`

Snippet: `samples/mathlib/mathlib-0345.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SSet.Truncated.mapFundamentalGroupoid_obj_mk
- **file**: Mathlib/AlgebraicTopology/SimplicialSet/FundamentalGroupoid/Basic.lean
- **derivation**: Truncated.mapFundamentalGroupoid_obj_mk ((truncation 2).map f) x
- **explanation**: The truncated lemma at line 189 of the same file says `(mapFundamentalGroupoid f).obj (.mk x) = .mk (f.app _ x)` for a morphism `f` of 2-truncated simplicial sets. The target is the same statement for `SSet`. The SSet version of `mapFundamentalGroupoid` is defined as the truncated one applied to `(truncation 2).map f`. The target therefore follows by taking `f := (truncation 2).map f` in the truncated lemma, up to definitional unfolding. The target's current proof is `rfl` and does not cite the truncated lemma. I did not search outside this file for other candidates.

### [`Set.Finite.infsep_pos_iff_nontrivial`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/MetricSpace/Infsep.lean#L464-L466) — `mathlib-0346`

Snippet: `samples/mathlib/mathlib-0346.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Set.infsep_pos_iff_nontrivial_of_finite
- **file**: Mathlib/Topology/MetricSpace/Infsep.lean
- **derivation**: haveI := hs.to_subtype; exact infsep_pos_iff_nontrivial_of_finite
- **proof_uses_it**: True
- **explanation**: The same file has `Set.infsep_pos_iff_nontrivial_of_finite [Finite s] : 0 < s.infsep ↔ s.Nontrivial`, stated for a metric space. It is the same statement as the target. The only difference is that the finiteness hypothesis is an instance (`Finite ↥s`) instead of an explicit `s.Finite`. The target's proof applies it after `hs.fintype`. It does not depend on the target, and it is not deprecated. I also checked the other `infsep_pos` lemmas in the file (`infsep_pos`, `nontrivial_of_infsep_pos`, `Finset.infsep_pos_iff_nontrivial`). None of them is a closer match.

### [`MeasureTheory.upperCrossingTime_eq_upperCrossingTime_of_lt`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Martingale/Upcrossing.lean#L497-L502) — `mathlib-0352`

Snippet: `samples/mathlib/mathlib-0352.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.crossing_eq_crossing_of_upperCrossingTime_lt
- **file**: Mathlib/Probability/Martingale/Upcrossing.lean
- **derivation**: cases n
· simp
· exact (crossing_eq_crossing_of_upperCrossingTime_lt hNM h).1
- **proof_uses_it**: True
- **explanation**: The target is the first conjunct of `crossing_eq_crossing_of_upperCrossingTime_lt` (which is stated for `n + 1` and proves the upper-crossing equality together with the lower-crossing one). The target's n = 0 case is closed by `simp`, since `upperCrossingTime _ _ _ _ 0 = ⊥`. The sibling lemma is a separate declaration that does not depend on the target; it is proved from `crossing_eq_crossing_of_lowerCrossingTime_lt`. I found no other Mathlib lemma that states the target directly. This match is the target's own proof, which wraps that lemma.

### [`CompactlySupportedContinuousMap.hasCompactSupport`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/ContinuousMap/CompactlySupported.lean#L83-L83) — `mathlib-0361`

Snippet: `samples/mathlib/mathlib-0361.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CompactlySupportedContinuousMapClass.hasCompactSupport
- **file**: Mathlib/Topology/ContinuousMap/CompactlySupported.lean
- **derivation**: CompactlySupportedContinuousMapClass.hasCompactSupport f
- **explanation**: The class `CompactlySupportedContinuousMapClass F α β` has the field `hasCompactSupport (f : F) : HasCompactSupport f`. The instance `CompactlySupportedContinuousMapClass C_c(α, β) α β` at line 85 is built from the structure projection `f.hasCompactSupport'`. It does not use the target lemma, so the class field is independent of it. Applying the class field to `f : C_c(α, β)` gives exactly the target statement `HasCompactSupport ⇑f`. The target is the same result, specialised to the structure type through the instance. I found no other candidate in the Mathlib file. I did not search Batteries or Lean core.

### [`Rat.inv_nonneg`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Field/Rat.lean#L46-L48) — `mathlib-0363`

Snippet: `samples/mathlib/mathlib-0363.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: inv_nonneg
- **file**: Mathlib/Algebra/Order/GroupWithZero/Basic.lean
- **derivation**: exact inv_nonneg.2 ha
- **explanation**: Mathlib's `inv_nonneg : 0 ≤ a⁻¹ ↔ 0 ≤ a` is stated for a `GroupWithZero` with a `PartialOrder` and `PosMulReflectLT`. Instantiating it at ℚ gives `Rat.inv_nonneg` as `inv_nonneg.2 ha`. The only uses of `Rat.inv_nonneg` and `Rat.div_nonneg` are in this same file, in the `NNRat` instances, so `inv_nonneg` does not depend on the target. The `Rat.inv_nonneg` lemma sits in a foundational file that is imported before the order instances, so it could not use `inv_nonneg` there. That affects only import order, not the correspondence of the statements. Lean core has only `Rat.inv_pos`, with no nonneg version. Batteries has neither.

### [`FirstOrder.Language.Term.realize_liftAt`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/ModelTheory/Semantics.lean#L92-L97) — `mathlib-0364`

Snippet: `samples/mathlib/mathlib-0364.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FirstOrder.Language.Term.realize_relabel
- **file**: Mathlib/ModelTheory/Semantics.lean
- **derivation**: realize_relabel
- **proof_uses_it**: True
- **explanation**: Term.liftAt n' m t is defined as t.relabel (Sum.map id fun i => if ↑i < m then castAdd n' i else addNat i n'). The target is realize_relabel, `(t.relabel g).realize v = t.realize (v ∘ g)`, with that specific g. The library's proof is exactly `realize_relabel`, with liftAt unfolded definitionally. The general lemma is a separate declaration that carries the content. I only looked at the other `realize_liftAt` and `realize_relabel` lemmas in the same file. The BoundedFormula and Formula versions are different statements.

### [`ContDiffAt.fst'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/ContDiff/Comp.lean#L320-L323) — `mathlib-0366`

Snippet: `samples/mathlib/mathlib-0366.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContDiffAt.fst''
- **file**: Mathlib/Analysis/Calculus/ContDiff/Comp.lean
- **derivation**: ContDiffAt.fst'' (x := (x, y)) hf
- **explanation**: ContDiffAt.fst'' states the same for an arbitrary point p : E × F with hypothesis ContDiffAt at p.1. Instantiating p := (x, y) gives fst' (p.1 reduces definitionally to x). Its proof is independent (hf.comp x contDiffAt_fst), so it doesn't use fst'. Both are in the same file.

### [`Real.arsinh_pos_iff`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Arsinh.lean#L152-L154) — `mathlib-0370`

Snippet: `samples/mathlib/mathlib-0370.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.arsinh_lt_arsinh
- **file**: Mathlib/Analysis/SpecialFunctions/Arsinh.lean
- **derivation**: by simpa using arsinh_lt_arsinh (x := 0) (y := x)
- **explanation**: The theorem `0 < arsinh x ↔ 0 < x` is `Real.arsinh_lt_arsinh : arsinh x < arsinh y ↔ x < y` with x := 0, using `arsinh_zero` (a simp lemma) to rewrite `arsinh 0` to `0`. `arsinh_lt_arsinh` is proved from `sinhOrderIso.symm.lt_iff_lt`, so it does not depend on `arsinh_pos_iff`. The current proof instead goes through `arsinh_nonpos_iff` with `lt_iff_lt_of_le_iff_le`. I did not search other Mathlib files, since this sibling lemma already matches.

### [`Cardinal.toENat_ofNat`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/SetTheory/Cardinal/ENat.lean#L249-L249) — `mathlib-0373`

Snippet: `samples/mathlib/mathlib-0373.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: map_ofNat
- **file**: Mathlib/Data/Nat/Cast/Basic.lean
- **derivation**: map_ofNat toENat n
- **explanation**: `Cardinal.toENat` is a bundled ordered ring hom `Cardinal →+*o ℕ∞`, so it is a `RingHomClass`. The generic `map_ofNat (f : F) (n) [n.AtLeastTwo] : f (OfNat.ofNat n) = OfNat.ofNat n` instantiated at `f := toENat` gives the target statement. The current proof uses `toENat_nat`, which is itself `map_natCast`, so it takes a parallel route and never applies `map_ofNat`.

### [`BddOrd.ext`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Category/BddOrd.lean#L96-L98) — `mathlib-0378`

Snippet: `samples/mathlib/mathlib-0378.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.ConcreteCategory.hom_ext
- **file**: Mathlib/CategoryTheory/ConcreteCategory/Basic.lean
- **derivation**: ConcreteCategory.hom_ext _ _ w
- **proof_uses_it**: True
- **explanation**: `ConcreteCategory.hom_ext {X Y : C} (f g : X ⟶ Y) (w : ∀ x, f x = g x) : f = g` is the general extensionality lemma for morphisms in any concrete category. `BddOrd.ext` is that lemma with C := BddOrd. The existing proof is already this one application. I only read that statement. I did not search for other candidates.

### [`Polynomial.support_add`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Polynomial/Basic.lean#L422-L423) — `mathlib-0384`

Snippet: `samples/mathlib/mathlib-0384.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finsupp.support_add
- **file**: Mathlib/Algebra/Group/Finsupp.lean
- **derivation**: simpa [support] using! Finsupp.support_add
- **proof_uses_it**: True
- **explanation**: Polynomial.support p is defined as p.toFinsupp.support, and addition on polynomials is addition of the underlying finsupps. So the statement is Finsupp.support_add transported through that definition. The library's own proof is already this one-line unfolding with `simpa [support] using!`. The other `support_add` lemmas I found (MvPolynomial, SkewPolynomial, SkewMonoidAlgebra) are sibling statements for different types and are not the same declaration.

### [`MeasureTheory.convolutionExistsAt_iff_integrable_swap`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Convolution.lean#L374-L376) — `mathlib-0386`

Snippet: `samples/mathlib/mathlib-0386.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.convolutionExistsAt_flip
- **file**: Mathlib/Analysis/Convolution.lean
- **derivation**: convolutionExistsAt_flip.symm
- **proof_uses_it**: True
- **explanation**: `convolutionExistsAt_flip` (line 364) says `ConvolutionExistsAt g f x L.flip μ ↔ ConvolutionExistsAt f g x L μ`. Its proof is independent of the target. Unfolding `ConvolutionExistsAt` turns the left side into `Integrable (fun t => L.flip (g t) (f (x - t))) μ`, and `L.flip (g t) (f (x - t))` is defeq to `L (f (x - t)) (g t)`. So the target is that lemma read backwards, with the definition unfolded. The target is a thin presentation wrapper around it. I found no other Mathlib declaration that states the unfolded form directly.

### [`ContinuousAt.div'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/Group/Defs.lean#L147-L150) — `mathlib-0389`

Snippet: `samples/mathlib/mathlib-0389.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Filter.Tendsto.div'
- **file**: Mathlib/Topology/Algebra/Group/Defs.lean
- **derivation**: Filter.Tendsto.div' hf hg
- **proof_uses_it**: True
- **explanation**: `Filter.Tendsto.div'` (line 141) says that if `f → 𝓝 a` and `g → 𝓝 b` along `l`, then `fun x => f x / g x → 𝓝 (a / b)`. Take `l = 𝓝 x`, `a = f x` and `b = g x`. Since `ContinuousAt f x` unfolds to `Tendsto f (𝓝 x) (𝓝 (f x))`, and `(f / g) x` is definitionally `f x / g x`, this gives `ContinuousAt (f / g) x`. The current proof `hf.div' hg` is nonrec, so it resolves to `Filter.Tendsto.div'` through that unfolding. I did not search further, since the library's own proof already settles the match.

### [`Topology.IsClosedEmbedding.isCompact_preimage`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Compactness/Compact.lean#L1015-L1018) — `mathlib-0392`

Snippet: `samples/mathlib/mathlib-0392.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsProperMap.isCompact_preimage
- **file**: Mathlib/Topology/Maps/Proper/Basic.lean
- **derivation**: hf.isProperMap.isCompact_preimage hK
- **explanation**: Mathlib has `IsProperMap.isCompact_preimage`: the preimage of a compact set under a proper map is compact. It also has `Topology.IsClosedEmbedding.isProperMap` (Proper/Basic.lean:274), so a closed embedding is proper. The target follows by applying the two in turn. Both are independent of the target. `isProperMap_of_isClosedMap_of_inj` is proved through compact fibers, and `IsProperMap.isCompact_preimage` is proved via ultrafilters. The current proof instead uses `Topology.IsInducing.isCompact_preimage` (Compact.lean:1001), which takes an inducing map with closed range. That declaration is another special-case source, since a closed embedding is inducing with closed range.

### [`PNat.mk_le_mk`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/PNat/Defs.lean#L95-L100) — `mathlib-0400`

Snippet: `samples/mathlib/mathlib-0400.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subtype.mk_le_mk
- **file**: Mathlib/Order/Basic.lean
- **derivation**: Subtype.mk_le_mk
- **proof_uses_it**: True
- **explanation**: ℕ+ is defined as the subtype {n : ℕ // 0 < n}, and its order is induced from ℕ's. Subtype.mk_le_mk says (⟨x, hx⟩ : Subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y, and it is a simp lemma proved by Iff.rfl. Taking α := ℕ and p := (0 < ·) gives PNat.mk_le_mk. The current `by simp` almost certainly closes the goal with this lemma. I did not check the instance unification, so `Subtype.mk_le_mk` may need `by exact` or `Iff.rfl`.

### [`emultiplicity_of_unit_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/Multiplicity.lean#L475-L476) — `mathlib-0403`

Snippet: `samples/mathlib/mathlib-0403.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: emultiplicity_of_isUnit_right
- **file**: Mathlib/RingTheory/Multiplicity.lean
- **derivation**: emultiplicity_of_isUnit_right ha u.isUnit
- **proof_uses_it**: True
- **explanation**: `emultiplicity_of_isUnit_right {a b : α} (ha : ¬IsUnit a) (hb : IsUnit b) : emultiplicity a b = 0` is the general statement. The target is the case b = ↑u for a unit u : αˣ, with hb given by `u.isUnit`. This is a different declaration in the same file, and the current proof already applies it. I only searched this file and the grep for the related names.

### [`EReal.natCast_ne_iff`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/EReal/Basic.lean#L811-L812) — `mathlib-0404`

Snippet: `samples/mathlib/mathlib-0404.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.cast_inj
- **file**: Mathlib/Algebra/CharZero/Defs.lean
- **derivation**: Nat.cast_inj.not
- **explanation**: EReal derives `CharZero` and `AddCommMonoidWithOne` (Mathlib/Data/EReal/Basic.lean, lines 36-37). The general `Nat.cast_inj : (m : R) = n ↔ m = n` for `[AddMonoidWithOne R] [CharZero R]` therefore applies to `R = EReal`. Negating both sides, with `.not` or `not_congr`, gives `natCast_ne_iff`. The local `natCast_eq_iff` is itself just `Nat.cast_inj` at `EReal`. The library's proof uses `natCast_eq_iff` through `not_iff_not`, not `Nat.cast_inj`. I found no dedicated `Nat.cast_ne_cast` lemma in Mathlib, so I'm calling this a special case.

### [`one_sup`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/IsBotOne.lean#L150-L151) — `mathlib-0416`

Snippet: `samples/mathlib/mathlib-0416.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sup_eq_right
- **file**: Mathlib/Order/Lattice.lean
- **derivation**: sup_eq_right.mpr one_le
- **proof_uses_it**: True
- **explanation**: The proof is `by simp`, which uses the simp lemma `one_le` from the same file and the generic lattice fact `sup_eq_right : a ⊔ b = b ↔ a ≤ b`. So `one_sup` is `sup_eq_right` with `a := 1`, plus `one_le` (`1 ≤ a`). I did not open `Mathlib/Order/Lattice.lean` to check the file path or the exact statement of `sup_eq_right`; both are from memory. `one_le` is not a Mathlib duplicate, because it is the defining property of `IsBotOneClass`, a class declared in this file. A grep for `one_sup`, `zero_sup`, `sup_one` and `sup_zero` found no independent Mathlib lemma of this form. The nearest hit was `Finset.sup_one` in `Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean`, which is a different statement. This verdict is a judgement call: the only generic Mathlib content is the lattice lemma.

### [`ValueDistribution.logCounting_add_const`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean#L503-L509) — `mathlib-0417`

Snippet: `samples/mathlib/mathlib-0417.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ValueDistribution.logCounting_add_analyticOn
- **file**: Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean
- **derivation**: logCounting_add_analyticOn hf analyticOn_const
- **proof_uses_it**: True
- **explanation**: logCounting_add_analyticOn states logCounting (f + g) ⊤ = logCounting f ⊤ for meromorphic f and g analytic on univ. Taking g = fun _ ↦ a₀ (constant, hence analytic) gives the target. The declaration is distinct and independent: its proof goes through negPart_divisor_add_of_analyticNhdOn_right. The target's docstring itself calls it a special case.

### [`Polynomial.support_X_pow`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Polynomial/Basic.lean#L816-L819) — `mathlib-0420`

Snippet: `samples/mathlib/mathlib-0420.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.support_monomial
- **file**: Mathlib/Algebra/Polynomial/Basic.lean
- **derivation**: by rw [X_pow_eq_monomial, support_monomial n one_ne_zero]
- **proof_uses_it**: True
- **explanation**: I found no separate declaration for the support of `X ^ n` over `R[X]`. The skew-polynomial and `MvPolynomial` versions are about different types. `Polynomial.support_monomial n (h : a ≠ 0) : (monomial n a).support = singleton n` gives the result with `a = 1`, using `X_pow_eq_monomial n : X ^ n = monomial n 1`. The side condition `(1 : R) ≠ 0` follows from `[Nontrivial R]` via `one_ne_zero`. The current proof already does this through `convert`, so the theorem is a short instantiation of `support_monomial`. `support_monomial` is declared at line 741 of the same file, but it is a distinct declaration.

### [`Set.subset_iUnion₂_of_subset`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Set/Lattice/Indexed.lean#L174-L178) — `mathlib-0423`

Snippet: `samples/mathlib/mathlib-0423.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: le_iSup₂_of_le
- **file**: Mathlib/Order/CompleteLattice/Basic.lean
- **derivation**: le_iSup₂_of_le i j h
- **proof_uses_it**: True
- **explanation**: `le_iSup₂_of_le` (line 230) says `a ≤ f i j → a ≤ ⨆ i, ⨆ j, f i j` in any complete lattice. Instantiated at the complete lattice `Set α`, `≤` is `⊆` and `⨆` is `⋃`, so it gives the theorem up to defeq. The existing proof is exactly this term. I found no other declaration with the `Set` statement. The name `subset_iUnion₂_of_subset` appears only here and in uses of it.

### [`MvPolynomial.eval₂_comp`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/MvPolynomial/Eval.lean#L436-L438) — `mathlib-0424`

Snippet: `samples/mathlib/mathlib-0424.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPolynomial.eval₂_comp_left
- **file**: Mathlib/Algebra/MvPolynomial/Eval.lean
- **derivation**: by rw [← eval₂_id]; simpa using eval₂_comp_left f (RingHom.id R) g p
- **explanation**: `eval₂_comp_left k f g p : k (eval₂ f g p) = eval₂ (k.comp f) (k ∘ g) p`. Take k := f (the target's f), f := RingHom.id R. Since `eval g p = eval₂ (RingHom.id _) g p` (`eval₂_id`, reversed) and `f.comp (RingHom.id R) = f` (`RingHom.comp_id`), this gives `f (eval g p) = eval₂ f (f ∘ g) p`. The theorem is thus the `eval₂_comp_left` statement with the inner ring hom set to the identity. A second route is `(map_eval f g p).trans (eval_map f (f ∘ g) p)`. The current proof uses `eval_map` and `eval₂_comp_right` instead.

### [`even_iff_two_dvd`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Ring/Parity.lean#L76-L76) — `mathlib-0425`

Snippet: `samples/mathlib/mathlib-0425.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: even_iff_exists_two_mul
- **file**: Mathlib/Algebra/Ring/Parity.lean
- **derivation**: by rw [even_iff_exists_two_mul]; rfl
- **explanation**: `even_iff_exists_two_mul : Even a ↔ ∃ b, a = 2 * b` is in the same file and is a distinct declaration. It is proved from `even_iff_exists_two_nsmul`, so it doesn't depend on the target. In a semiring, `2 ∣ a` unfolds by definition (`semigroupDvd`) to `∃ c, a = 2 * c`, so the target is that lemma with `Dvd` unfolded. The current proof is `simp [Even, Dvd.dvd, two_mul]` and doesn't use it. I found no other declaration stating `Even a ↔ 2 ∣ a` in Mathlib or Batteries. Only the lemma itself and its uses showed up in a grep.

### [`Finite.exists_max`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Fintype/Lattice.lean#L51-L54) — `mathlib-0427`

Snippet: `samples/mathlib/mathlib-0427.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Filter.Tendsto.exists_forall_ge
- **file**: Mathlib/Order/Filter/Cofinite.lean
- **derivation**: Filter.Tendsto.exists_forall_ge (by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot)
- **explanation**: Filter.Tendsto.exists_forall_ge has the form [Nonempty α] [LinearOrder β] {f : α → β} (hf : Tendsto f cofinite atBot) : ∃ a₀, ∀ a, f a ≤ f a₀. When α is finite, cofinite = ⊥ (Filter.cofinite_eq_bot), so the hypothesis holds by Filter.tendsto_bot. The conclusion is exactly the target statement. The current proof goes through Finset.exists_max_image instead. Other nearby results do not match: Finite.exists_le only gives an upper bound that need not be attained, and Set.Finite.exists_maximalFor gives Maximal, which needs more work to convert.

### [`ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map₀'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Independence/InfinitePi.lean#L78-L84) — `mathlib-0428`

Snippet: `samples/mathlib/mathlib-0428.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ProbabilityTheory.iIndepFun.map_fun_eq_infinitePi_map₀
- **file**: Mathlib/Probability/Independence/InfinitePi.lean
- **derivation**: h.map_fun_eq_infinitePi_map₀ (aemeasurable_pi_iff.2 mX)
- **proof_uses_it**: True
- **explanation**: The conclusion is the same, but the hypothesis differs. The target assumes each X i is AEMeasurable and ι is countable. `iIndepFun.map_fun_eq_infinitePi_map₀` assumes that the joint map `fun ω i ↦ X i ω` is AEMeasurable. The target follows in one line by converting the hypothesis with `aemeasurable_pi_iff`, which is how the current proof works. This is a thin wrapper, not an independent duplicate. `iIndepFun_iff_map_fun_eq_infinitePi_map₀'` also gives it via `.mp`, but it needs an extra `IsProbabilityMeasure P` assumption. I found no other declaration with the same statement.

### [`not_prime_one`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Prime/Defs.lean#L98-L99) — `mathlib-0431`

Snippet: `samples/mathlib/mathlib-0431.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Prime.ne_one
- **file**: Mathlib/Algebra/Prime/Defs.lean
- **derivation**: fun h => h.ne_one rfl
- **explanation**: `Prime.ne_one` (line 63, same file) says `Prime p → p ≠ 1`. Taking p = 1 gives `¬Prime 1` as `fun h => h.ne_one rfl`. Its proof doesn't depend on `not_prime_one`; it uses `hp.2.1` and `isUnit_one`. Other matches: `Nat.not_prime_one` (Mathlib/Data/Nat/Prime/Defs.lean) is only the ℕ version, and `not_irreducible_one` is about Irreducible, not Prime.

### [`LocallyConstant.mulIndicator_apply_eq_if`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/LocallyConstant/Basic.lean#L464-L468) — `mathlib-0433`

Snippet: `samples/mathlib/mathlib-0433.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.mulIndicator_apply
- **file**: Mathlib/Algebra/Notation/Indicator.lean
- **derivation**: Set.mulIndicator_apply U f a
- **proof_uses_it**: True
- **explanation**: `LocallyConstant.mulIndicator f hU` is defined with `toFun := Set.mulIndicator U f`. Its value at `a` is therefore defeq to `Set.mulIndicator U f a`. `Set.mulIndicator_apply` states `mulIndicator s f a = if a ∈ s then f a else 1`, which is the target statement with `s := U`. The current proof is that one-line application, plus unfolding the definition. This is not a clean duplicate: the target is about the locally constant bundled version, not `Set.mulIndicator` itself. I searched `Mathlib/Algebra/Notation/Indicator.lean` and grepped for other `mulIndicator_apply` lemmas. I found nothing closer.

### [`AddChar.zpow_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/AddChar.lean#L412-L412) — `mathlib-0438`

Snippet: `samples/mathlib/mathlib-0438.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddChar.zsmul_apply
- **file**: Mathlib/Algebra/Group/AddChar.lean
- **derivation**: zsmul_apply ..
- **proof_uses_it**: True
- **explanation**: AddChar.zsmul_apply (line 409) says (n • ψ) a = ψ a ^ n. The theorem is the multiplicative version, (ψ ^ n) a = ψ a ^ n. On AddChar A M the additive group structure is defined from the CommGroup structure (line 365), so n • ψ and ψ ^ n are defeq. The current proof is just `zsmul_apply ..`. It is a different declaration, stated with `•` instead of `^`, and it carries the real content (its proof is the `cases n <;> simp` argument). I found no other match in Mathlib.

### [`ContinuousLinearMap.continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean#L142-L144) — `mathlib-0439`

Snippet: `samples/mathlib/mathlib-0439.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContinuousMapClass.map_continuous
- **file**: Mathlib/Topology/ContinuousMap/Defs.lean
- **derivation**: map_continuous f
- **explanation**: I did not open the file that defines `ContinuousMapClass`, so the path above is my best guess. I only confirmed that `map_continuous` is used in `Mathlib/Topology/ContinuousMap/Basic.lean`. It is the field `map_continuous (f : F) : Continuous f` of the class `ContinuousMapClass F α β`. `ContinuousLinearMap.continuousSemilinearMapClass` extends this class. Its `map_continuous` field is proved directly as `f.2`, so the instance does not depend on `ContinuousLinearMap.continuous`. The theorem is therefore `map_continuous f` with `F := M₁ →SL[σ₁₂] M₂`, which instance search fills in. The current proof uses `f.2`, the structure projection, and does not use `map_continuous`.

### [`Set.image_inv_Ico`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Group/Pointwise/Interval.lean#L369-L370) — `mathlib-0444`

Snippet: `samples/mathlib/mathlib-0444.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.inv_Ico
- **file**: Mathlib/Algebra/Order/Group/Pointwise/Interval.lean
- **derivation**: by rw [← Set.image_inv_eq_inv]; exact Set.inv_Ico a b ▸ rfl
-- or simply: by simpa [← Set.image_inv_eq_inv] using Set.inv_Ico a b
- **proof_uses_it**: True
- **explanation**: Set.inv_Ico says (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹ (pointwise inverse of a set). The target is the same statement with the pointwise inverse written as the image Inv.inv '' _. Set.image_inv_eq_inv ((·⁻¹) '' s = s⁻¹) converts between the two forms. Both lemmas are simp lemmas, which is why the existing `by simp` proof works. The target is therefore a restatement of inv_Ico in image form, derived with one rewrite. A better derivation would be `by rw [Set.image_inv_eq_inv, Set.inv_Ico]`.

### [`Equiv.prodComm_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Logic/Equiv/Prod.lean#L92-L94) — `mathlib-0454`

Snippet: `samples/mathlib/mathlib-0454.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Equiv.coe_prodComm
- **file**: Mathlib/Logic/Equiv/Prod.lean
- **derivation**: congrFun (coe_prodComm α β) x
- **explanation**: `Equiv.coe_prodComm` (line 89, same file) states `⇑(prodComm α β) = Prod.swap` and is proved by `rfl`, independently of the target. The target is its pointwise form, so `congrFun` gives it. The current proof is `rfl`. I found no other declaration in Mathlib, Batteries or Lean core that states the pointwise form.

### [`Pi.Lex.lt_iff_of_unique`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/PiLex.lean#L104-L106) — `mathlib-0460`

Snippet: `samples/mathlib/mathlib-0460.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Pi.lex_iff_of_unique
- **file**: Mathlib/Order/PiLex.lean
- **derivation**: lex_iff_of_unique
- **proof_uses_it**: True
- **explanation**: `Pi.lex_iff_of_unique` (line 69 of the same file) states `Pi.Lex r (· < ·) x y ↔ x default < y default` for `Unique ι` and `[Std.Irrefl r]`. The target is the case r = (· < ·) on `Lex (∀ i, β i)`, where `<` unfolds definitionally to `Pi.Lex (· < ·) (· < ·)`. Preorder ι supplies the `Std.Irrefl (· < ·)` instance. The target's proof is just `lex_iff_of_unique`, which does not depend on the target. The target is a thin wrapper over a separate earlier lemma, so I count it as a special case and not a standalone result. I found no other candidate in Mathlib, Batteries or core.

### [`MeasureTheory.condExp_mul_of_stronglyMeasurable_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean#L250-L254) — `mathlib-0464`

Snippet: `samples/mathlib/mathlib-0464.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: MeasureTheory.condExp_mul_of_aestronglyMeasurable_right
- **file**: Mathlib/MeasureTheory/Function/ConditionalExpectation/PullOut.lean
- **derivation**: condExp_mul_of_aestronglyMeasurable_right hg.aestronglyMeasurable hfg hf
- **explanation**: `condExp_mul_of_aestronglyMeasurable_right` (PullOut.lean, line 240) has the same statement as the target. Its only difference is a weaker hypothesis: `AEStronglyMeasurable[m] g μ` instead of `StronglyMeasurable[m] g`. The conclusion `μ[f * g | m] =ᵐ[μ] μ[f | m] * g` and the integrability hypotheses are identical. The target's proof calls the more general `condExp_bilin_of_aestronglyMeasurable_right` directly, not this lemma. The derivation above needs only the coercion `hg.aestronglyMeasurable`. This lemma does not depend on the target, because its proof uses `condExp_bilin_of_aestronglyMeasurable_right`.

### [`MeasureTheory.IsProbabilityMeasure.ae_neBot`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean#L90-L90) — `mathlib-0465`

Snippet: `samples/mathlib/mathlib-0465.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.Measure.ae_neBot
- **file**: Mathlib/MeasureTheory/Measure/Filter.lean
- **derivation**: ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
- **proof_uses_it**: True
- **explanation**: The target's proof is `inferInstance`. It resolves through the instance `[NeZero μ] : (ae μ).NeBot` (Filter.lean:47), which is proved from `ae_neBot : (ae μ).NeBot ↔ μ ≠ 0` (Filter.lean:44). The instance at Probability.lean:88 supplies `NeZero μ` from `IsProbabilityMeasure`. So the target follows from `ae_neBot` and `IsProbabilityMeasure.ne_zero` in one line. I did not check that `ae_neBot` sits in the `MeasureTheory.Measure` namespace, so the qualified name is a guess. The `NeZero` instance sits just above the target, in the same file as `IsProbabilityMeasure.ne_zero`. The `ae_neBot` lemma itself does not depend on the target.

### [`RingHom.IsIntegralElem.of_mul_unit`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean#L207-L210) — `mathlib-0470`

Snippet: `samples/mathlib/mathlib-0470.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsIntegral.of_mul_unit
- **file**: Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean
- **derivation**: letI : Algebra R S := f.toAlgebra
IsIntegral.of_mul_unit hr hx
- **proof_uses_it**: True
- **explanation**: `IsIntegral.of_mul_unit` is the same statement for an algebra `R → B`. The theorem is its instance with `B := S` and the algebra structure `f.toAlgebra`, where `f.IsIntegralElem` unfolds to `IsIntegral`. `IsIntegral.of_mul_unit` has its own direct proof via `scaleRoots`, so it does not depend on the theorem being judged. Its only other uses are in Localization/Integral.lean and Jacobson/Ring.lean.

### [`MeasureTheory.lintegral_zero_fun`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean#L116-L117) — `mathlib-0471`

Snippet: `samples/mathlib/mathlib-0471.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: MeasureTheory.lintegral_zero
- **file**: Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean
- **derivation**: lintegral_zero
- **proof_uses_it**: True
- **explanation**: `lintegral_zero` (line 114) states `∫⁻ _ : α, 0 ∂μ = 0`, which is `lintegral μ (fun _ => 0) = 0`. The target states the same thing with `(0 : α → ℝ≥0∞)` in place of `fun _ => 0`. These are definitionally equal, and the current proof is exactly `lintegral_zero`. Only the way the zero function is written differs. The match is an independent declaration, and its proof is `by simp`, which does not depend on the target.

### [`Set.ncard_strictMono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Set/Card.lean#L896-L897) — `mathlib-0475`

Snippet: `samples/mathlib/mathlib-0475.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Set.card_strictMono
- **file**: Mathlib/SetTheory/Cardinal/NatCard.lean
- **derivation**: Set.card_strictMono  -- ncard s = Nat.card s is rfl (Nat.card_coe_set_eq); else: fun s t h ↦ by simpa using Set.card_strictMono h
- **explanation**: Set.card_strictMono ([Finite α] : StrictMono (α := Set α) (Nat.card ∘ (↑))) states the same thing as Set.ncard_strictMono. Set.ncard s is by definition Nat.card ↥s: Nat.card_coe_set_eq is proved by rfl at Card.lean:653. The two statements differ only by that definitional unfolding. The Mathlib proof is `fun _ t ↦ t.toFinite.card_lt_card`, which does not depend on ncard_strictMono. The current proof uses ncard_lt_ncard instead.

### [`max_left_commutative`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/MinMax.lean#L152-L153) — `mathlib-0477`

Snippet: `samples/mathlib/mathlib-0477.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: instLeftCommutativeOfCommutativeOfAssociative (anonymous instance `{f : α → α → α} [Std.Commutative f] [Std.Associative f] : LeftCommutative f`)
- **file**: Mathlib/Logic/OpClass.lean
- **derivation**: inferInstance
- **explanation**: Mathlib/Logic/OpClass.lean line 61 has a general instance: `Std.Commutative f` and `Std.Associative f` give `LeftCommutative f`. The instance name is auto-generated, so I am guessing it. Mathlib/Order/MinMax.lean lines 149-150 (`instCommutativeMax`, `instAssociativeMax`) give both hypotheses for `max` on a linear order. Those two instances are separate from the target theorem, so they are independent evidence. Instantiating `f := max` therefore gives the target, and `inferInstance` should find it. The current proof instead uses `⟨max_left_comm⟩`.

### [`Finset.sum_prod_piFinset`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/BigOperators/Ring/Finset.lean#L161-L163) — `mathlib-0485`

Snippet: `samples/mathlib/mathlib-0485.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.prod_univ_sum
- **file**: Mathlib/Algebra/BigOperators/Ring/Finset.lean
- **derivation**: exact (prod_univ_sum (fun _ : ι ↦ s) g).symm
- **proof_uses_it**: True
- **explanation**: `Finset.prod_univ_sum` (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → R) states `∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ piFinset t, ∏ i, f i (x i)`. Taking the constant family `t := fun _ => s` and `f := g` and swapping the sides gives the target. The current proof is `rw [← prod_univ_sum]`, which applies the same lemma.

### [`Finset.coe_eq_one`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean#L84-L85) — `mathlib-0487`

Snippet: `samples/mathlib/mathlib-0487.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.coe_eq_singleton
- **file**: Mathlib/Data/Finset/Insert.lean
- **derivation**: coe_eq_singleton
- **proof_uses_it**: True
- **explanation**: Finset.coe_eq_singleton states (s : Set α) = {a} ↔ s = {a}. Taking a = 1 gives the target, since the pointwise `1` on Set and Finset is definitionally `{1}`. The current proof is exactly this term.

### [`Equiv.Perm.sameCycle_comm`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/GroupTheory/Perm/Cycle/Basic.lean#L69-L70) — `mathlib-0491`

Snippet: `samples/mathlib/mathlib-0491.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: comm
- **file**: Mathlib/Order/Defs/Unbundled.lean
- **derivation**: haveI := (SameCycle.equivalence f).stdSymm
exact comm
- **explanation**: The root-namespace theorem `comm [Std.Symm r] {a b : α} : r a b ↔ r b a` (Mathlib/Order/Defs/Unbundled.lean:329) has proof `⟨symm, symm⟩`, the same as the target. Taking `r := SameCycle f` gives the target. The `Std.Symm` instance comes from `Equivalence.stdSymm` applied to `SameCycle.equivalence f`, which Mathlib already has. I found no instance of `Std.Symm (SameCycle f)`, so the derivation builds it inline, which is why this is a special case and not a duplicate. I found no other `SameCycle`-specific version of this lemma, and I did not check whether the `comm` declaration is itself deprecated or an alias. I searched `SameCycle.comm`, `Equivalence.*comm`, `Symmetric.*iff`, and `Std.Symm`/`IsSymm` in `GroupTheory/Perm`.

### [`Cardinal.not_isSuccLimit_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/SetTheory/Cardinal/Order.lean#L417-L419) — `mathlib-0498`

Snippet: `samples/mathlib/mathlib-0498.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Order.not_isSuccLimit_bot
- **file**: Mathlib/Order/SuccPred/Limit.lean
- **derivation**: not_isSuccLimit_bot
- **proof_uses_it**: True
- **explanation**: `Order.not_isSuccLimit_bot [OrderBot α] : ¬ IsSuccLimit (⊥ : α)` specialised to `α = Cardinal`, where `0 = ⊥` holds definitionally. The target's proof is exactly this declaration. I also found `Ordinal.not_isSuccLimit_zero`, which is the Ordinal analogue and not relevant here.

### [`ContinuousOn.piecewise'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Piecewise.lean#L65-L70) — `mathlib-0499`

Snippet: `samples/mathlib/mathlib-0499.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContinuousOn.if'
- **file**: Mathlib/Topology/Piecewise.lean
- **derivation**: hf.if' hpf hpg hg
- **proof_uses_it**: True
- **explanation**: `ContinuousOn.if'` is the same statement for `fun a => if p a then f a else g a` with `{a | p a}` in place of `t`. Taking `p := (· ∈ t)` gives `{a | a ∈ t} = t` definitionally, and `piecewise t f g a = if a ∈ t then f a else g a` by definition. So `ContinuousOn.piecewise'` is that instance. It is a separate declaration, and its proof does not depend on `piecewise'`. The library's own proof is the one-line `hf.if' hpf hpg hg`. I found no other declaration matching this statement. A grep of Mathlib for `ContinuousOn.piecewise'` and `ContinuousOn.if'` found only this file.

### [`AddConstMapClass.map_sub_int`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/AddConstMap/Basic.lean#L239-L240) — `mathlib-0506`

Snippet: `samples/mathlib/mathlib-0506.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddConstMapClass.map_sub_int'
- **file**: Mathlib/Algebra/AddConstMap/Basic.lean
- **derivation**: by simpa using map_sub_int' f x n
- **proof_uses_it**: True
- **explanation**: `map_sub_int'` (line 235, same file) states `f (x - n) = f x - n • b` for `AddConstMapClass F G H 1 b`, with H only an AddGroup. Taking b = 1 gives `n • (1 : H)`, and `zsmul_one` (a simp lemma) turns that into `(n : H)`. The current `by simp` proof already uses it, because it is a scoped simp lemma in this namespace. I found no other declaration elsewhere in Mathlib that states this; a grep for `AddConstMapClass F G H 1 1` only returns lemmas in this file.

### [`Antitone.cauchySeq_alternating_series_of_tendsto_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecificLimits/Normed.lean#L953-L958) — `mathlib-0508`

Snippet: `samples/mathlib/mathlib-0508.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
- **file**: Mathlib/Analysis/SpecificLimits/Normed.lean
- **derivation**: simp_rw [mul_comm]
exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le
- **proof_uses_it**: True
- **explanation**: The theorem is the alternating series test for antitone f. The current proof instantiates Mathlib's general Dirichlet-type test `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` with z i = (-1)^i and bound 1. It gets that bound from `norm_sum_neg_one_pow_le`, which sits in the same file. It also rewrites with `mul_comm`. I read both the neighbouring `Monotone.cauchySeq_alternating_series_of_tendsto_zero` and the proof of the target. The Monotone version is a different statement, so it doesn't count. I found no other Mathlib declaration that states the alternating series Cauchy test for antitone sequences. This is a judgement call: the derivation depends on the helper lemma `norm_sum_neg_one_pow_le`, so a stricter reading could answer `none_found`.

### [`AddCircle.liftIco_zero_continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Instances/AddCircle/Defs.lean#L840-L842) — `mathlib-0511`

Snippet: `samples/mathlib/mathlib-0511.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddCircle.liftIco_continuous
- **file**: Mathlib/Topology/Instances/AddCircle/Defs.lean
- **derivation**: liftIco_continuous (by rwa [zero_add] : f 0 = f (0 + p)) (by rwa [zero_add])
- **proof_uses_it**: True
- **explanation**: `AddCircle.liftIco_continuous` has the same statement with a general base point `a`, with hypotheses `f a = f (a + p)` and `ContinuousOn f (Icc a (a + p))`. The target is the case `a = 0`. Rewriting with `zero_add` converts `0 + p` to `p`, and that is the only glue needed. The library's current proof is exactly this. It sits in the same file and does not depend on the target.

### [`Affine.Simplex.affineCombination_mem_interior_face_iff_mem_Ioo`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/AffineSpace/Simplex/Basic.lean#L568-L572) — `mathlib-0512`

Snippet: `samples/mathlib/mathlib-0512.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Affine.Simplex.affineCombination_mem_setInterior_face_iff_mem
- **file**: Mathlib/LinearAlgebra/AffineSpace/Simplex/Basic.lean
- **derivation**: affineCombination_mem_setInterior_face_iff_mem _ _ _ hw
- **proof_uses_it**: True
- **explanation**: The general lemma gives, for any I : Set k, membership in (s.face h).setInterior I iff (∀ i ∈ fs, w i ∈ I) ∧ (∀ i ∉ fs, w i = 0). Taking I = Set.Ioo 0 1 gives the target, since `interior` is `setInterior (Set.Ioo 0 1)`. The current proof is this one-line instantiation. I did not open the definition of `interior` to confirm that unfolding, but the current proof relies on it.

### [`TopCat.ofHom_hom`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/TopCat/Basic.lean#L132-L134) — `mathlib-0514`

Snippet: `samples/mathlib/mathlib-0514.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.ConcreteCategory.ofHom_hom
- **file**: Mathlib/CategoryTheory/ConcreteCategory/Basic.lean
- **derivation**: ConcreteCategory.ofHom_hom f
- **explanation**: TopCat.ofHom and TopCat.Hom.hom are abbrevs for ConcreteCategory.ofHom (C := TopCat) and ConcreteCategory.hom (C := TopCat). So the statement is the general field `ConcreteCategory.ofHom_hom` (ofHom (hom f) = f), a simp lemma, specialized to the ConcreteCategory instance on TopCat. The current proof is `rfl`, not a call to that declaration. The elaborated statement `ofHom (Hom.hom f) : of X ⟶ of Y` is defeq to `X ⟶ Y`, so the term applies.

### [`Irreducible.normalizedFactors_pow`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean#L174-L177) — `mathlib-0521`

Snippet: `samples/mathlib/mathlib-0521.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: UniqueFactorizationMonoid.normalizedFactors_of_irreducible_pow
- **file**: Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean
- **derivation**: exact normalizedFactors_of_irreducible_pow hp k
- **explanation**: At line 215 of the same file, `normalizedFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : ℕ) : normalizedFactors (p ^ k) = Multiset.replicate k (normalize p)` has the same statement as the target, in the same namespace and under the same typeclass assumptions. Its proof is the same rewrite chain and does not use the target. I found no deprecation attribute on it.

### [`RelSeries.toList_getElem_zero_eq_head`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/RelSeries.lean#L259-L260) — `mathlib-0526`

Snippet: `samples/mathlib/mathlib-0526.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: RelSeries.head_toList
- **file**: Mathlib/Order/RelSeries.lean
- **derivation**: by rw [← p.head_toList, List.head_eq_getElem]
- **explanation**: `RelSeries.head_toList` says `p.toList.head p.toList_ne_nil = p.head`. The target says `p.toList[0] = p.head`. The two differ only in how the first element of the list is written: `List.head` against `l[0]`. Core's `List.head_eq_getElem` (`head l h = l[0]'_`) converts between them. `head_toList` is proved by `simp [toList, apply_zero]`, so it does not depend on the target. The derivation needs `head_toList` plus that core lemma and one `rw`, so it is a short special case rather than a verbatim duplicate. I did not find a declaration that states the `getElem 0` form directly. I searched RelSeries.lean and Mathlib for `getElem_zero_eq_head`, and Core's list lemmas. I did not check the `rw` by running Lean.

### [`mul_right_strictMono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean#L134-L136) — `mathlib-0528`

Snippet: `samples/mathlib/mathlib-0528.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: StrictMono.const_mul'
- **file**: Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean
- **derivation**: strictMono_id.const_mul' a
- **explanation**: `StrictMono.const_mul'` (line 955 of the same file) says that if `f` is strictly monotone and `[MulLeftStrictMono α]` holds, then `fun x => c * f x` is strictly monotone. Taking `f = id` gives `mul_right_strictMono`, because `fun x => a * id x` is defeq to `(a * ·)`. Its proof uses `mul_lt_mul_right` directly, not the target, so it is independent. The target is the `f = id` instance. Other matches are specific to other types: the `FractionalIdeal` version and the `ENat` and `ENNReal` versions have extra hypotheses. I did not find an exact duplicate.

### [`TensorProduct.congrL_mul_mul`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/InnerProductSpace/TensorProduct.lean#L768-L769) — `mathlib-0529`

Snippet: `samples/mathlib/mathlib-0529.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TensorProduct.congrL_trans_trans
- **file**: Mathlib/Analysis/InnerProductSpace/TensorProduct.lean
- **derivation**: congrL_trans_trans ..
- **proof_uses_it**: True
- **explanation**: `congrL_trans_trans` (line 758) is stated for E ≃L F ≃L F₂ and G ≃L H ≃L H₂: `congrL (f₁.trans f₂) (g₁.trans g₂) = (congrL f₁ g₁).trans (congrL f₂ g₂)`. Multiplication in `E ≃L[𝕜] E` is `trans` with the arguments swapped, so `congrL_mul_mul` is the case where F = E, H = G, F₂ = E and H₂ = G. It is proved by exactly this lemma. `congrL_trans_trans` is a separate declaration, and its proof (`ext; simp [congrL, map_map]`) does not depend on `congrL_mul_mul`. I found no other Mathlib lemma for this statement. A grep for `congrL_mul_mul` and `congrL_trans_trans` returned only this file.

### [`MeasureTheory.AEStronglyMeasurable.comp_snd_map_prod_id`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Kernel/Condexp.lean#L46-L50) — `mathlib-0534`

Snippet: `samples/mathlib/mathlib-0534.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.AEStronglyMeasurable.comp_snd_map_prodMk
- **file**: Mathlib/Probability/Kernel/CondDistrib.lean
- **derivation**: hf.comp_snd_map_prodMk (@Measurable.aemeasurable Ω Ω mΩ m id μ (measurable_id'' hm))
- **proof_uses_it**: True
- **explanation**: The general lemma `comp_snd_map_prodMk` says that for X : Ω → β AE-measurable and f AE-strongly measurable, `fun x : β × Ω => f x.2` is AE-strongly measurable w.r.t. `μ.map (fun ω => (X ω, ω))`. The target takes β = Ω with the sub-σ-algebra m and X = id. Then `fun ω => (id ω, ω)` is `Function.diag`, which is defeq to it. The only extra input is the measurability of `id` from `mΩ` to `m`, which comes from `measurable_id''`. The current proof is exactly this one-line instantiation.

### [`Subfield.extendScalars_toSubfield`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/IntermediateField/Basic.lean#L801-L802) — `mathlib-0539`

Snippet: `samples/mathlib/mathlib-0539.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subfield.toIntermediateField_toSubfield
- **file**: Mathlib/FieldTheory/IntermediateField/Basic.lean
- **derivation**: Subfield.toIntermediateField_toSubfield E _
- **explanation**: Subfield.extendScalars h is defined as E.toIntermediateField (fun ⟨_, hf⟩ ↦ h hf). The lemma Subfield.toIntermediateField_toSubfield says (S.toIntermediateField _).toSubfield = S, so the target follows by unfolding extendScalars and applying it with S := E. It holds by rfl in both places. The current proof uses SetLike.coe_injective rfl instead. I found no other declaration in Mathlib, Batteries or Lean core that states the target more directly.

### [`MonoidHom.fst_mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Monoid/Lex.lean#L49-L51) — `mathlib-0547`

Snippet: `samples/mathlib/mathlib-0547.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: monotone_fst
- **file**: Mathlib/Order/Monotone/Defs.lean
- **derivation**: exact monotone_fst
- **explanation**: `monotone_fst : Monotone (@Prod.fst α β)` for preorders α, β. `MonoidHom.fst α β` coerces to `Prod.fst` definitionally (`MonoidHom.coe_fst`). So the goal is `monotone_fst` after unfolding the coercion. If `exact` does not close it, `simpa using monotone_fst` should. The Monoid assumptions are not needed.

### [`UniformSpace.Completion.denseRange_coe₂`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/UniformSpace/Completion.lean#L383-L385) — `mathlib-0553`

Snippet: `samples/mathlib/mathlib-0553.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: DenseRange.prodMap
- **file**: Mathlib/Topology/Constructions/SumProd.lean
- **derivation**: denseRange_coe.prodMap denseRange_coe
- **proof_uses_it**: True
- **explanation**: `DenseRange.prodMap` says that if f and g have dense range, then `Prod.map f g` has dense range. Take f = coe : α → Completion α and g = coe : β → Completion β. Both are dense by `UniformSpace.Completion.denseRange_coe`, which is also a Mathlib declaration. The function `fun x => (↑x.1, ↑x.2)` is `Prod.map` of the two coercions, so the existing one-line proof is the whole derivation.

### [`MvPolynomial.cardinalMk_eq_one`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/MvPolynomial/Cardinal.lean#L45-L46) — `mathlib-0554`

Snippet: `samples/mathlib/mathlib-0554.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Cardinal.mk_eq_one
- **file**: Mathlib/SetTheory/Cardinal/Defs.lean
- **derivation**: mk_eq_one _
- **proof_uses_it**: True
- **explanation**: `Cardinal.mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α] : #α = 1` is the general statement. The theorem is the instance α := MvPolynomial σ R. It needs the `Subsingleton (MvPolynomial σ R)` and `Nonempty` instances, which come from `Subsingleton R` and the ring structure. The current proof is exactly `mk_eq_one _`. I found no MvPolynomial-specific duplicate. `FreeAlgebra.cardinalMk_eq_one` is a different type.

### [`NNRat.floor_cast`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/NNRat/Floor.lean#L58-L60) — `mathlib-0557`

Snippet: `samples/mathlib/mathlib-0557.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.map_floor
- **file**: Mathlib/Algebra/Order/Floor/Semiring.lean
- **derivation**: Nat.map_floor (NNRat.castHom K) NNRat.cast_strictMono x
- **explanation**: `Nat.map_floor` says that for a ring hom `f : R →+* S` between linear ordered semirings with `FloorSemiring` instances, if `f` is strictly monotone then `⌊f a⌋₊ = ⌊a⌋₊`. Take `R = ℚ≥0` (with its `FloorSemiring` instance from this file), `S = K`, and `f = NNRat.castHom K` (Mathlib/Data/Rat/Cast/CharZero.lean). `NNRat.cast_strictMono` (Mathlib/Data/Rat/Cast/Order.lean) gives strict monotonicity. The ring hom coerces to `(↑) : ℚ≥0 → K` definitionally, so this is exactly `floor_cast`. I did not read the typeclass assumptions of `NNRat.cast_strictMono`, only its location. I expect them to match `floor_cast`'s (`Semifield`, `LinearOrder`, `IsStrictOrderedRing`). The derivation is one line.

### [`Monotone.mulIndicator_eventuallyEq_iUnion`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Filter/IndicatorFunction.lean#L66-L70) — `mathlib-0559`

Snippet: `samples/mathlib/mathlib-0559.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Monotone.piecewise_eventually_eq_iUnion
- **file**: Mathlib/Order/Filter/AtTopBot/Defs.lean
- **derivation**: classical exact hs.piecewise_eventually_eq_iUnion f 1 a
- **proof_uses_it**: True
- **explanation**: Monotone.piecewise_eventually_eq_iUnion states ∀ᶠ i in atTop, (s i).piecewise f g a = (⋃ i, s i).piecewise f g a for a monotone family s. Taking g = 1 and unfolding mulIndicator s f = s.piecewise f 1 (with classical decidability) gives the target. The existing proof is exactly this one-line instantiation. I found no other declaration with the same statement.

### [`UnitAddCircle.integral_preimage`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean#L251-L255) — `mathlib-0563`

Snippet: `samples/mathlib/mathlib-0563.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddCircle.integral_preimage
- **file**: Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean
- **derivation**: AddCircle.integral_preimage 1 t f
- **proof_uses_it**: True
- **explanation**: UnitAddCircle is AddCircle (1 : ℝ). The theorem is AddCircle.integral_preimage (line 188 of the same file) with T = 1, and the current proof is exactly that application. This is a different declaration and its proof doesn't depend on the target.

### [`LinearIsometry.preimage_sphere`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Operator/LinearIsometry.lean#L262-L264) — `mathlib-0575`

Snippet: `samples/mathlib/mathlib-0575.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Isometry.preimage_sphere
- **file**: Mathlib/Topology/MetricSpace/Isometry.lean
- **derivation**: f.isometry.preimage_sphere x r
- **proof_uses_it**: True
- **explanation**: Isometry.preimage_sphere (hf : Isometry f) (x) (r) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r holds for any isometry. The target is that statement for the underlying function of a linear isometry f, with hf given by f.isometry. The current proof is exactly that one-line application.

### [`PrimeMultiset.coeNat_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/PNat/Factors.lean#L71-L72) — `mathlib-0578`

Snippet: `samples/mathlib/mathlib-0578.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Multiset.map_injective
- **file**: Mathlib/Data/Multiset/MapFold.lean
- **derivation**: Multiset.map_injective Subtype.val_injective
- **proof_uses_it**: True
- **explanation**: PrimeMultiset is a def for Multiset Nat.Primes, and the coercion to Multiset ℕ is Multiset.map (↑). The statement is therefore Multiset.map_injective with f the coercion Nat.Primes → ℕ, which is injective by Nat.Primes.coe_nat_injective (or Subtype.val_injective). The current proof is exactly this one-line application. I found no other Mathlib declaration that states injectivity of the PrimeMultiset coercion.

### [`Real.monotone_rpow_of_base_ge_one`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean#L906-L910) — `mathlib-0579`

Snippet: `samples/mathlib/mathlib-0579.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Real.rpow_le_rpow_of_exponent_le
- **file**: Mathlib/Analysis/SpecialFunctions/Pow/Real.lean
- **derivation**: fun _ _ h => Real.rpow_le_rpow_of_exponent_le hb h
- **explanation**: `Real.rpow_le_rpow_of_exponent_le (hx : 1 ≤ x) (hyz : y ≤ z) : x ^ y ≤ x ^ z` is the pointwise form of `Monotone (b ^ · : ℝ → ℝ)` under `1 ≤ b`. Unfolding `Monotone` gives the one-line derivation. It is proved at line 617 from `rpow_def_of_pos`, `exp_le_exp` and `log_nonneg`, so it does not depend on the target lemma. The target's own proof uses `strictMono_rpow_of_base_gt_one` and a case split instead.

### [`Finset.union_assoc`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Finset/Lattice/Basic.lean#L142-L143) — `mathlib-0582`

Snippet: `samples/mathlib/mathlib-0582.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sup_assoc
- **file**: Mathlib/Order/Defs/Lattice.lean
- **derivation**: sup_assoc _ _ _
- **proof_uses_it**: True
- **explanation**: `sup_assoc` says `a ⊔ b ⊔ c = a ⊔ (b ⊔ c)` in any semilattice. On `Finset α` with `DecidableEq`, `∪` is `⊔` by definition, so the theorem is `sup_assoc` at `Finset α`. The library's own proof is exactly `sup_assoc _ _ _`. I found no other candidate. A grep for sup_assoc turned up only this declaration and a BooleanRing-specific one.

### [`RelIso.sumLexComplRight_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Hom/Lex.lean#L68-L70) — `mathlib-0584`

Snippet: `samples/mathlib/mathlib-0584.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: RelIso.sumLexComplRight_symm_apply
- **file**: Mathlib/Order/Hom/Lex.lean
- **derivation**: sumLexComplRight_symm_apply a
- **explanation**: In the same file (line 73), `RelIso.sumLexComplRight_symm_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap` is stated with exactly the same type and the same variables and instances as `sumLexComplRight_apply`. It is probably a copy-paste slip: the name suggests `.symm` was intended. It is a distinct declaration, and it is proved by `rfl`, so it does not depend on the target. I searched for other mentions of `sumLexComplRight` in Mathlib. The only other one is its use in `OrderIso.sumLexIicIoi`. Apart from this twin, the lemma is only the definitional unfolding of the library's own def.

### [`Finite.card_eq_zero_iff`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/SetTheory/Cardinal/NatCard.lean#L89-L91) — `mathlib-0588`

Snippet: `samples/mathlib/mathlib-0588.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.card_eq_zero
- **file**: Mathlib/SetTheory/Cardinal/Finite.lean
- **derivation**: Nat.card_eq_zero.trans (or_iff_left Infinite.false)
- **explanation**: Mathlib has `Nat.card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α`, with no finiteness assumption. Given `[Finite α]`, the disjunct `Infinite α` is impossible, because `Infinite.false : [Finite α] → Infinite α → False`. So `or_iff_left` reduces the disjunction to `IsEmpty α`. The derivation is one line and I did not compile it. Two other lemmas are close but do not match. `Fintype.card_eq_zero_iff` is for `Fintype.card`, and the current proof already uses it. `Cardinal.card_eq_zero_iff_empty` is for ordinal/cardinal `card`.

### [`Finset.union_smul_inter_subset_union`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/Pointwise/Finset/Scalar.lean#L137-L139) — `mathlib-0595`

Snippet: `samples/mathlib/mathlib-0595.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.image₂_union_inter_subset_union
- **file**: Mathlib/Data/Finset/NAry.lean
- **derivation**: image₂_union_inter_subset_union
- **proof_uses_it**: True
- **explanation**: Finset.image₂_union_inter_subset_union says image₂ f (s ∪ s') (t ∩ t') ⊆ image₂ f s t ∪ image₂ f s' t' for any binary function f. The pointwise scalar product s • t on finsets is defined as image₂ (· • ·) s t, so the target is that lemma with f := (· • ·). The current proof is exactly this term. The multiplicative and division versions in Finset/Basic.lean are proved the same way.

### [`CategoryTheory.Limits.hasPullback_unop_iff_hasPushout`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Opposites/Pullbacks.lean#L320-L324) — `mathlib-0608`

Snippet: `samples/mathlib/mathlib-0608.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.hasPushout_op_iff_hasPullback
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Opposites/Pullbacks.lean
- **derivation**: (hasPushout_op_iff_hasPullback f.unop g.unop).symm
- **explanation**: The target is `HasPullback f.unop g.unop ↔ HasPushout f g` for `f g` in `Cᵒᵖ`. Apply `hasPushout_op_iff_hasPullback` (in the same file) to `f.unop` and `g.unop` in `C`. This gives `HasPushout f.unop.op g.unop.op ↔ HasPullback f.unop g.unop`. Here `f.unop.op = f` holds by `rfl`, so `.symm` finishes it. I did not check the elaboration, since I can't run Lean; a `simpa using` with `Quiver.Hom.op_unop` is the fallback if the defeq doesn't unify. The library's own proof goes through `cospanUnop` and `hasLimit_leftOp_iff_hasColimit` instead. I found no other declaration with this exact statement.

### [`LieSubmodule.coe_neg`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Lie/Submodule.lean#L162-L164) — `mathlib-0609`

Snippet: `samples/mathlib/mathlib-0609.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: NegMemClass.coe_neg
- **file**: Mathlib/Algebra/Group/Subgroup/Defs.lean
- **derivation**: exact NegMemClass.coe_neg m
- **explanation**: NegMemClass.coe_neg is the additive version of InvMemClass.coe_inv. For any SetLike S G with NegMemClass, it states (-x : H).1 = -x.1 for x : H. LieSubmodule R L M has an AddSubgroupClass instance (Lie/Submodule.lean line 59), so NegMemClass applies directly. That gives exactly ↑(-m) = -↑m. The current proof is rfl and does not use it. I did not confirm that the Neg instance on ↥N is the same one NegMemClass uses, but the two are definitionally equal by rfl.

### [`LieModule.IsIrreducible.mk`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Lie/Semisimple/Defs.lean#L36-L39) — `mathlib-0615`

Snippet: `samples/mathlib/mathlib-0615.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsSimpleOrder.of_forall_eq_top
- **file**: Mathlib/Order/Atoms.lean
- **derivation**: IsSimpleOrder.of_forall_eq_top h
- **proof_uses_it**: True
- **explanation**: `LieModule.IsIrreducible R L M` is an abbrev for `IsSimpleOrder (LieSubmodule R L M)`. `IsSimpleOrder.of_forall_eq_top` states that a nontrivial bounded order with `a ≠ ⊥ → a = ⊤` for all `a` is a simple order. Taking `α := LieSubmodule R L M` gives the theorem. The `Nontrivial (LieSubmodule R L M)` instance comes from `Nontrivial M` by instance search. The existing proof is exactly this application.

### [`ContinuousLinearMap.continuousOn_uncurry_of_multilinear`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean#L97-L99) — `mathlib-0620`

Snippet: `samples/mathlib/mathlib-0620.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContinuousLinearMap.continuous_uncurry_of_multilinear
- **file**: Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean
- **derivation**: f.continuous_uncurry_of_multilinear.continuousOn
- **proof_uses_it**: True
- **explanation**: The target is the restriction to a set s of the global continuity statement `ContinuousLinearMap.continuous_uncurry_of_multilinear` (same hypotheses, line 93, same file). It follows from that lemma plus `Continuous.continuousOn`, which is a one-line derivation. The target's own proof is exactly that, so it's a thin wrapper around a distinct declaration. I found no other Mathlib declaration with this statement.

### [`Condensed.hom_ext`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Condensed/Basic.lean#L57-L61) — `mathlib-0624`

Snippet: `samples/mathlib/mathlib-0624.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Sheaf.hom_ext
- **file**: Mathlib/CategoryTheory/Sites/Sheaf.lean
- **derivation**: exact Sheaf.hom_ext (NatTrans.ext (funext h))
- **proof_uses_it**: True
- **explanation**: Condensed C is an abbrev for Sheaf (coherentTopology CompHaus) C. The lemma says two sheaf morphisms are equal if they agree on every component. Sheaf.hom_ext gives equality from f.hom = g.hom, and NatTrans.ext (funext h) gives f.hom = g.hom from componentwise equality. The existing proof uses `ext`, which applies Sheaf.hom_ext, so it already relies on this declaration. I did not check how `ext` resolves it.

### [`Rat.isInt_round`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Rat/Floor.lean#L279-L280) — `mathlib-0632`

Snippet: `samples/mathlib/mathlib-0632.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: round_intCast
- **file**: Mathlib/Algebra/Order/Round.lean
- **derivation**: rintro ⟨⟨⟩⟩; exact ⟨by rw [round_intCast]; rfl⟩
- **explanation**: `IsInt r m` unfolds to `r = (m : R)`. After substituting, the goal `IsInt (round (m : R)) m` reduces to `round (m : R) = m` (with the ℤ→ℤ cast). `round_intCast (n : ℤ) : round (n : α) = n` states exactly that for a ring with a linear order and floor ring, which matches `R` here. So the theorem is a norm_num wrapper around `round_intCast`. The current proof's `simp` presumably closes the goal with `round_intCast`, but it doesn't name it. I searched Mathlib for other `IsInt (round …)` or `isInt_floor`-style lemmas and found none, so this is the only match.

### [`WithSeminorms.withSeminorms_eq`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean#L312-L314) — `mathlib-0633`

Snippet: `samples/mathlib/mathlib-0633.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: WithSeminorms.topology_eq_withSeminorms
- **file**: Mathlib/Analysis/LocallyConvex/WithSeminorms.lean
- **derivation**: hp.topology_eq_withSeminorms
- **proof_uses_it**: True
- **explanation**: The theorem restates the single field of the structure `WithSeminorms`, namely `topology_eq_withSeminorms : topology = p.moduleFilterBasis.topology`. The current proof `hp.1` is that projection. The projection is a separate declaration with the same statement, and it is available independently. I found no other Mathlib declaration with this statement. I grepped for `moduleFilterBasis.topology` and `withSeminorms_eq` and read the structure definition.

### [`Complex.isQuotientCoveringMap_npow`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Complex/CoveringMap.lean#L118-L120) — `mathlib-0634`

Snippet: `samples/mathlib/mathlib-0634.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: isQuotientCoveringMap_npow
- **file**: Mathlib/Analysis/Complex/CoveringMap.lean
- **derivation**: isQuotientCoveringMap_npow n (by simp [NeZero.ne]) fun _ ↦ ⟨_, cpow_nat_inv_pow _ (NeZero.ne n)⟩
- **proof_uses_it**: True
- **explanation**: The general `isQuotientCoveringMap_npow` is stated for a nontrivially normed, proper-space field 𝕜. It needs (n : 𝕜) ≠ 0 and surjectivity of x ↦ x^n. Taking 𝕜 = ℂ gives the target statement. The target's proof is exactly this instantiation, with the two side conditions closed by `simp` and `cpow_nat_inv_pow`. The general lemma is a separate declaration in the same file, and its proof does not depend on the target. I also looked at `Circle.isQuotientCoveringMap_npow`, which concerns the circle rather than ℂˣ, so it is not a match.

### [`Int.fract_sub_intCast`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Floor/Ring.lean#L411-L414) — `mathlib-0635`

Snippet: `samples/mathlib/mathlib-0635.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Int.fract_add_intCast
- **file**: Mathlib/Algebra/Order/Floor/Ring.lean
- **derivation**: by rw [sub_eq_add_neg, ← Int.cast_neg, Int.fract_add_intCast]
- **explanation**: `Int.fract_add_intCast` says `fract (a + m) = fract a` for any integer `m`. Instantiating `m := -m` and rewriting `a - m` as `a + ((-m : ℤ) : R)` gives `fract_sub_intCast`. The proof of `fract_add_intCast` (`rw [fract]; simp`) does not depend on the target. I found no declaration with the identical statement. The sibling lemmas `fract_sub_natCast`, `fract_sub_one` and `fract_sub_ofNat` are in the same file and are not independent of it. The current proof is `rw [fract]; simp`, so it does not use `fract_add_intCast`.

### [`AddValuation.IsEquiv.val_eq`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/Valuation/Basic.lean#L1338-L1339) — `mathlib-0637`

Snippet: `samples/mathlib/mathlib-0637.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Valuation.IsEquiv.eq_iff
- **file**: Mathlib/RingTheory/Valuation/Basic.lean
- **derivation**: Valuation.IsEquiv.eq_iff h
- **proof_uses_it**: True
- **explanation**: `AddValuation.IsEquiv v₁ v₂` is defined as `Valuation.IsEquiv v₁ v₂`. Here an `AddValuation` is a `Valuation` into `Multiplicative Γ₀ᵒᵈ`. `Valuation.IsEquiv.eq_iff` (line 738) states `v₁ r = v₁ s ↔ v₂ r = v₂ s` for `h : v₁.IsEquiv v₂`. That is the same statement, so the theorem is the multiplicative lemma instantiated at the order-dual multiplicative codomain. The current proof is exactly this one-line application. I did not search for any other candidate.

### [`hasDerivWithinAt_inter'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L400-L402) — `mathlib-0638`

Snippet: `samples/mathlib/mathlib-0638.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: hasFDerivWithinAt_inter'
- **file**: Mathlib/Analysis/Calculus/FDeriv/Basic.lean
- **derivation**: hasFDerivWithinAt_inter' h
- **proof_uses_it**: True
- **explanation**: HasDerivWithinAt f f' s x unfolds to HasFDerivWithinAt f (smulRight 1 f') s x. The Fréchet-derivative lemma hasFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) : HasFDerivWithinAt f f' (s ∩ t) x ↔ HasFDerivWithinAt f f' s x, with E := 𝕜 and f' := smulRight 1 f', gives the statement directly. The library's proof is exactly this one-line application. I did not find a separate 1-D declaration in Mathlib; the only other hits were hasDerivWithinAt_inter, which takes t ∈ 𝓝 x, and hasDerivWithinAt_congr_set.

### [`IntermediateField.minpoly_gen`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean#L411-L413) — `mathlib-0643`

Snippet: `samples/mathlib/mathlib-0643.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IntermediateField.minpoly_eq
- **file**: Mathlib/FieldTheory/IntermediateField/Algebraic.lean
- **derivation**: by rw [IntermediateField.minpoly_eq, AdjoinSimple.coe_gen]
- **explanation**: `IntermediateField.minpoly_eq (S : IntermediateField K L) (x : S) : minpoly K x = minpoly K (x : L)`. Taking S = F⟮α⟯ and x = AdjoinSimple.gen F α gives the goal up to `AdjoinSimple.coe_gen`, which is `rfl`, so `IntermediateField.minpoly_eq _` may also close it directly. The library's proof uses `minpoly.algebraMap_eq` and `AdjoinSimple.algebraMap_gen` instead, and `minpoly_eq` itself is proved independently from `minpoly.algebraMap_eq`. I did not find a declaration that states `minpoly_gen` itself.

### [`Subgroup.Commensurable.smul`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/GroupTheory/Commensurable.lean#L121-L123) — `mathlib-0644`

Snippet: `samples/mathlib/mathlib-0644.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.Commensurable.map
- **file**: Mathlib/GroupTheory/Commensurable.lean
- **derivation**: h.map (MulDistribMulAction.toMonoidHom G φ)
- **proof_uses_it**: True
- **explanation**: `Subgroup.Commensurable.map (f : G →* G') (h : H.Commensurable K) : Commensurable (H.map f) (K.map f)`. The pointwise action `φ • H` for `MulDistribMulAction` is defeq to `H.map (MulDistribMulAction.toMonoidHom G φ)`. So the target follows by instantiating `f` with that hom, which is what the current proof `h.map _` does. I found no other declaration in Mathlib, Batteries or core that states this. The other uses of it are downstream of the target.

### [`Polynomial.degree_list_sum_le_of_forall_degree_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Polynomial/BigOperators.lean#L84-L93) — `mathlib-0645`

Snippet: `samples/mathlib/mathlib-0645.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.mem_degreeLE
- **file**: Mathlib/RingTheory/Polynomial/Basic.lean
- **derivation**: exact (Polynomial.mem_degreeLE (R := S)).1 (list_sum_mem fun p hp => Polynomial.mem_degreeLE.2 (hl p hp))
- **explanation**: Polynomial.degreeLE R n is a Submodule R R[X] whose members are exactly the polynomials with degree ≤ n (mem_degreeLE : f ∈ degreeLE R n ↔ degree f ≤ n). The theorem says a list of polynomials that all lie in this submodule has its sum in it too. That is the generic list_sum_mem (additive closure of a submodule, in Mathlib/Algebra/Group/Submonoid/BigOperators.lean) applied to degreeLE S n. The derivation above converts to membership with mem_degreeLE, applies list_sum_mem, and converts back. The current proof instead does a manual induction using degree_add_le. I found no Mathlib lemma with this exact statement: the neighbouring ones (degree_sum_le, natDegree_sum_le_of_forall_le, degree_list_sum_le) are different. I did not check that mem_degreeLE can be used at this point in the import order.

### [`Set.univ_pi_piecewise_univ`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Set/Piecewise.lean#L181-L182) — `mathlib-0650`

Snippet: `samples/mathlib/mathlib-0650.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Set.pi_univ_ite
- **file**: Mathlib/Data/Set/Prod.lean
- **derivation**: exact Set.pi_univ_ite s t
- **proof_uses_it**: True
- **explanation**: `Set.pi_univ_ite` states `(pi univ fun i => if i ∈ s then t i else univ) = s.pi t` with `[DecidablePred (· ∈ s)]`. `s.piecewise t (fun _ => univ)` is definitionally `fun i => if i ∈ s then t i else univ`, so the target is the same statement with `piecewise` unfolded. The target's proof is `by simp`, which uses the simp lemma `pi_univ_ite` (after unfolding `piecewise` with `Set.piecewise_eq_ite`). `Set.univ_pi_ite` in the same file is a second copy of the same statement.

### [`AlgHom.map_adjoin`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean#L846-L847) — `mathlib-0651`

Snippet: `samples/mathlib/mathlib-0651.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Algebra.adjoin_image
- **file**: Mathlib/Algebra/Algebra/Subalgebra/Lattice.lean
- **derivation**: (Algebra.adjoin_image φ s).symm
- **proof_uses_it**: True
- **explanation**: Algebra.adjoin_image (f : A →ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R s).map f. The target is the same statement with the two sides of the equality swapped. The current proof is `(adjoin_image _ _ _).symm`. It is a distinct declaration, so it counts.

### [`Computable.vector_head`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Computability/Partrec.lean#L347-L348) — `mathlib-0656`

Snippet: `samples/mathlib/mathlib-0656.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Primrec.vector_head
- **file**: Mathlib/Computability/Primrec/List.lean
- **derivation**: Primrec.vector_head.to_comp
- **proof_uses_it**: True
- **explanation**: Primrec.vector_head states Primrec (@List.Vector.head α n). Computable.vector_head is the same statement with Computable in place of Primrec. The step between them is Primrec.to_comp, so the derivation is one line, and the current proof already uses it. I found no other Computable-level declaration about List.Vector.head. Searching Mathlib/Computability for Vector.head returned only these two.

### [`RingCon.quotientQuotientEquivQuotient_coe_coe`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/Congruence/Hom.lean#L379-L381) — `mathlib-0661`

Snippet: `samples/mathlib/mathlib-0661.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: RingCon.quotientQuotientEquivQuotient_mk_mk
- **file**: Mathlib/RingTheory/Congruence/Hom.lean
- **derivation**: quotientQuotientEquivQuotient_mk_mk c d h x
- **explanation**: The same file has `RingCon.quotientQuotientEquivQuotient_mk_mk` with the same hypotheses c, d, h, x. It states `c.quotientQuotientEquivQuotient d h ⟦⟦x⟧⟧ = ⟦x⟧`. The target states the same equation, except that the double quotient class of x is written with coercions `↑(x : c.Quotient)` instead of `⟦⟦x⟧⟧`. These are the same quotient classes, and both lemmas are proved by `rfl`. The `mk_mk` proof is `rfl`, so it doesn't depend on the target. The analogous `quotientQuotientEquivQuotientₐ_coe_coe` is proved by calling `quotientQuotientEquivQuotientₐ_mk_mk`, which suggests `coe_coe` is a restatement of `mk_mk`. I did not check how Lean elaborates the coercion against `⟦⟧` (whether the terms are syntactically equal or only defeq). Either way the derivation above should close the goal, since `exact` works up to defeq. The `Con` and `Setoid` versions have no such simp lemmas.

### [`CategoryTheory.MonoidalClosed.whiskerLeft_curry_ihom_ev_app`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean#L215-L219) — `mathlib-0663`

Snippet: `samples/mathlib/mathlib-0663.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.MonoidalClosed.uncurry_curry
- **file**: Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean
- **derivation**: by rw [← uncurry_eq, uncurry_curry]
- **explanation**: `uncurry_curry` says `uncurry (curry f) = f`. `uncurry_eq` (proved by `rfl`) unfolds `uncurry g` to `A ◁ g ≫ (ihom.ev A).app X`. So the target is `uncurry_curry` with `uncurry` unfolded. Both lemmas are earlier in the same file, and neither depends on the target. The current proof goes via `curry_eq` and `simp`, not through `uncurry_curry`.

### [`sInf_sup_le_iInf_sup`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/CompleteLattice/Lemmas.lean#L124-L127) — `mathlib-0665`

Snippet: `samples/mathlib/mathlib-0665.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: biInf_sup_le_biInf_sup
- **file**: Mathlib/Order/CompleteLattice/Lemmas.lean
- **derivation**: by rw [sInf_eq_iInf]; exact biInf_sup_le_biInf_sup id s a
- **explanation**: `biInf_sup_le_biInf_sup (f : β → α) (s : Set β) (a : α) : (⨅ i ∈ s, f i) ⊔ a ≤ ⨅ i ∈ s, f i ⊔ a` is a more general statement. Taking β = α and f = id gives the target once `sInf s` is rewritten as `⨅ b ∈ s, b` with `sInf_eq_iInf`. The target's own proof is a direct `le_iInf₂` argument. I found no other declaration with the same statement. The only other `sInf s ⊔ a` hits are the `sInf_sup_eq` and `sup_sInf_eq` references in the docstring and in LiminfLimsup.lean. I did not read `sInf_eq_iInf` itself. I only saw its dual `sSup_eq_iSup` in Order/CompleteLattice/Basic.lean, and `sInf_eq_iInf` presumably comes from the `to_dual` attribute there.

### [`groupCohomology.isIso_δ_of_isZero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RepresentationTheory/Homological/GroupCohomology/LongExactSequence.lean#L106-L108) — `mathlib-0671`

Snippet: `samples/mathlib/mathlib-0671.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.ShortComplex.ShortExact.isIso_δ
- **file**: Mathlib/Algebra/Homology/HomologySequence.lean
- **derivation**: exact (map_cochainsFunctor_shortExact hX).isIso_δ n (n + 1) rfl h hs
- **explanation**: The generic lemma says that for a short exact sequence S of homological complexes with c.Rel i j, if H_i(S.X₂) and H_j(S.X₂) are zero then the connecting map hS.δ i j hij is an isomorphism. Here it is applied to the short exact sequence of inhomogeneous cochain complexes (`map_cochainsFunctor_shortExact hX`), with i = n and j = n+1. `groupCohomology.δ` is by definition `(map_cochainsFunctor_shortExact hX).δ`, and `groupCohomology X.X₂ n` is the homology of the cochain complex, so `h` and `hs` should typecheck by defeq. The current proof uses the lower-level `SnakeInput.isIso_δ`, which this lemma itself wraps.

### [`Finset.union_left_comm`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Finset/Lattice/Basic.lean#L160-L161) — `mathlib-0672`

Snippet: `samples/mathlib/mathlib-0672.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sup_left_comm
- **file**: Mathlib/Order/Defs/Lattice.lean
- **derivation**: by simpa only [sup_eq_union] using sup_left_comm s t u
- **explanation**: Finset α is a lattice whose ⊔ is ∪ (Finset.sup_eq_union : s ⊔ t = s ∪ t). The general `sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c)` in a SemilatticeSup, instantiated at Finset α, gives the statement after rewriting with sup_eq_union. The current proof uses ext and mem_union instead. I did not find a separate Finset-specific duplicate; the only other union_left_comm is Set.union_left_comm.

### [`Real.cos_eq_cos_iff`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Trigonometric/Complex.lean#L305-L306) — `mathlib-0674`

Snippet: `samples/mathlib/mathlib-0674.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Complex.cos_eq_cos_iff
- **file**: Mathlib/Analysis/SpecialFunctions/Trigonometric/Complex.lean
- **derivation**: mod_cast @Complex.cos_eq_cos_iff x y
- **proof_uses_it**: True
- **explanation**: Complex.cos_eq_cos_iff (line 81) states the same iff for complex x y. The real statement is its restriction to real arguments, with the coercions removed by one `mod_cast`. This is the current proof. I found no other declaration. The `Angle` lemmas `cos_eq_iff_eq_or_eq_neg` and `Real.Angle.cos_eq_iff_coe_eq_or_eq_neg` (around line 194) state a different result, about `Real.Angle` equalities rather than `∃ k : ℤ`. I judged this a special_case rather than a duplicate because the two statements are about different types, ℂ and ℝ, and the transfer between them relies on cast lemmas.

### [`MvPowerSeries.finSuccEquiv_comp_C`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/MvPowerSeries/Equiv.lean#L210-L212) — `mathlib-0679`

Snippet: `samples/mathlib/mathlib-0679.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPowerSeries.finSuccEquiv_C
- **file**: Mathlib/RingTheory/MvPowerSeries/Equiv.lean
- **derivation**: ext1; simp [AlgEquiv.symm_apply_eq]
- **proof_uses_it**: True
- **explanation**: The target says that composing the inverse of finSuccEquiv with PowerSeries.C ∘ MvPowerSeries.C gives MvPowerSeries.C. `finSuccEquiv_C` (a simp lemma, a distinct declaration, 9 lines above) says `finSuccEquiv R n (C r) = PowerSeries.C (C r)`. The target is that statement rewritten with the inverse equiv and stated as a ring-hom equality. The current proof is `ext1; simp [AlgEquiv.symm_apply_eq]`, and the simp call uses `finSuccEquiv_C`. `finSuccEquiv_C` has its own direct proof and does not depend on the target. The same-named `MvPolynomial.finSuccEquiv_comp_C_eq_C` is for polynomials, so it is not a match. I found no MvPowerSeries declaration outside this file that states the target.

### [`MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_top`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean#L385-L390) — `mathlib-0687`

Snippet: `samples/mathlib/mathlib-0687.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_top_of_enorm
- **file**: Mathlib/MeasureTheory/Function/LpSeminorm/CompareExp.lean
- **derivation**: eLpNorm_le_eLpNorm_mul_eLpNorm_top_of_enorm p b c hb.comp_aestronglyMeasurable₂ hg (ae_enorm_bilin_le_of_ae_nnnorm_le h)
- **proof_uses_it**: True
- **explanation**: The target is the instantiation of the general enorm version (`eLpNorm_le_eLpNorm_mul_eLpNorm_top_of_enorm`, stated for ENormedAddMonoid types ε, ε', ε'' and c : ℝ≥0∞) to normed groups E, F, G with c : ℝ≥0. The measurability hypothesis `hb` is obtained from continuity of the uncurried `b`. The nnnorm bound is converted to an enorm bound by `ae_enorm_bilin_le_of_ae_nnnorm_le`. The conclusion is identical. Other declarations I found in the same file are the `_of_pos` variants, which need `0 < p` and are not duplicates. This is borderline: the derivation uses two Mathlib helper lemmas, which are more than routine glue, but it is a single short term. No other Mathlib declaration states the nnnorm-form result.

### [`Continuous.mulIndicator`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/Indicator.lean#L29-L32) — `mathlib-0689`

Snippet: `samples/mathlib/mathlib-0689.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: continuous_mulIndicator
- **file**: Mathlib/Topology/Algebra/Indicator.lean
- **derivation**: exact continuous_mulIndicator hs hf.continuousOn
- **explanation**: `continuous_mulIndicator` (line 25 of the same file) has the same frontier hypothesis `hs` and the same conclusion. It assumes only `ContinuousOn f (closure s)`, and `Continuous f` gives that through `hf.continuousOn`. Its proof uses `continuous_piecewise`, not the target, so it is independent. The current proof of the target uses `Continuous.piecewise` directly. Other declarations in the file, such as `IsClopen.continuous_mulIndicator`, are derived from the target, so they don't count.

### [`WeierstrassCurve.Projective.fin3_def_ext`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Basic.lean#L126-L127) — `mathlib-0691`

Snippet: `samples/mathlib/mathlib-0691.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: WeierstrassCurve.Jacobian.fin3_def_ext
- **file**: Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean
- **derivation**: WeierstrassCurve.Jacobian.fin3_def_ext a b c
- **explanation**: Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean line 126 has a distinct declaration `WeierstrassCurve.Jacobian.fin3_def_ext (a b c : R) : ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c] z = c`. It has the same statement, with the same local notation x, y, z for 0, 1, 2 : Fin 3. I did not read its proof, but its statement is identical to the target's and it is in a different namespace. It does not depend on the Projective lemma, which lives in a separate file. The statement is also covered by the simp lemmas `Matrix.cons_val_zero`, `Matrix.cons_val_one` and `Matrix.cons_val_two`, which are all `rfl`-based.

### [`List.getI_append`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/List/GetD.lean#L117-L118) — `mathlib-0701`

Snippet: `samples/mathlib/mathlib-0701.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: List.getD_append
- **file**: Mathlib/Data/List/GetD.lean
- **derivation**: getD_append _ _ default _ h
- **proof_uses_it**: True
- **explanation**: `List.getI n` is by definition `l.getD n default` (see `getD_default_eq_getI`, proved by `rfl`). `List.getD_append` states `(l ++ l').getD n d = l.getD n d` for `n < l.length`. Taking `d := default` gives the theorem, and the current proof does exactly that. `getD_append` is a separate declaration in the same file. I found no copy of it in Batteries or Lean core, and no other `getI_append` in Mathlib.

### [`Set.indicator_smul_const`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Module/Basic.lean#L158-L160) — `mathlib-0708`

Snippet: `samples/mathlib/mathlib-0708.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.indicator_smul_left
- **file**: Mathlib/Algebra/Module/Basic.lean
- **derivation**: indicator_smul_left s r (fun _ => m)
- **explanation**: `Set.indicator_smul_left` states `indicator s (fun a ↦ r a • f a) = fun a ↦ indicator s r a • f a` under the same `[Zero R] [Zero M] [SMulWithZero R M]` hypotheses. Taking `f := fun _ => m` gives the target up to beta reduction. The current proof reaches the same result through `Set.indicator_smul_const_apply`, which is also in Mathlib and is itself proved from `indicator_smul_apply_left`. I did not check whether that applies `indicator_smul_left` for `indicator_smul_const`.

### [`ContDiffAt.localInverse_apply_image`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean#L59-L61) — `mathlib-0710`

Snippet: `samples/mathlib/mathlib-0710.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HasStrictFDerivAt.localInverse_apply_image
- **file**: Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean
- **derivation**: (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image
- **proof_uses_it**: True
- **explanation**: The target is the C^n version of the local-inverse identity. `ContDiffAt.localInverse` is defined as `HasStrictFDerivAt.localInverse f f' a` applied to the strict derivative obtained from `hf.hasStrictFDerivAt' hf' hn`. The Mathlib theorem `HasStrictFDerivAt.localInverse_apply_image` states `hf.localInverse f f' a (f a) = a` for a strict derivative. The target follows from it in one line by supplying the strict derivative, and the current proof already does this. This is a thin wrapper rather than an identical statement, so I chose `special_case` over `duplicate`.

### [`CategoryTheory.types_comp`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Types/Basic.lean#L194-L196) — `mathlib-0714`

Snippet: `samples/mathlib/mathlib-0714.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.ConcreteCategory.coe_comp
- **file**: Mathlib/CategoryTheory/ConcreteCategory/Basic.lean
- **derivation**: exact ConcreteCategory.coe_comp f g
- **explanation**: `ConcreteCategory.coe_comp` (and the equivalent `CategoryTheory.hom_comp`) says that in any concrete category, `⇑(f ≫ g) = g ∘ f` as functions `ToType X → ToType Z`. Specialising `C := Type u` gives `types_comp`. Here `ToType X = X`, and the statement elaborates to the coerced function `⇑(ConcreteCategory.hom (f ≫ g)) = ⇑g ∘ ⇑f`. The library proves it by `rfl`, not by the general lemma. I did not check that the two statements unify at reducible transparency, so the match is likely rather than certain.

### [`Int.odd_coe_nat`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Ring/Int/Parity.lean#L88-L88) — `mathlib-0722`

Snippet: `samples/mathlib/mathlib-0722.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Int.natAbs_odd
- **file**: Mathlib/Algebra/Ring/Int/Parity.lean
- **derivation**: (Int.natAbs_odd (n := (n : ℤ))).symm
- **explanation**: `Int.natAbs_odd : Odd n.natAbs ↔ Odd n` with `n := (k : ℤ)` gives `Odd (k : ℤ).natAbs ↔ Odd (k : ℤ)`. `(k : ℤ).natAbs` is definitionally `k`, so the symmetric form is `Odd (k : ℤ) ↔ Odd k`. If the `exact` does not go through by defeq, `simpa only [Int.natAbs_natCast]` closes it. `Int.natAbs_odd` is a separate declaration proved by `grind`, with no dependence on `odd_coe_nat`. It is the only match: other lemmas in this area, such as `Odd.natCast`, are one-directional, and grepping for `Odd` with `Nat.cast`, `natCast` and `Int.odd` names found no iff statement about `Odd (n : ℤ)`. The case is borderline because the match sits in the same file as the target.

### [`Quiver.Path.weightOfEPs_pos`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Combinatorics/Quiver/Path/Weight.lean#L118-L124) — `mathlib-0723`

Snippet: `samples/mathlib/mathlib-0723.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Quiver.Path.weight_pos
- **file**: Mathlib/Combinatorics/Quiver/Path/Weight.lean
- **derivation**: exact weight_pos (fun _ => hw _ _) p
- **proof_uses_it**: True
- **explanation**: `weightOfEPs w` is defined as `weight (fun {i j} _ => w i j)`. Instantiating `weight_pos` at the edge-weight function `fun e => w i j` gives the claim. The hypothesis `∀ e, 0 < w i j` comes straight from `hw`. The current proof already does this with `apply weight_pos`. `weight_pos` is a different declaration in the same file and is proved independently by induction. I found no other matching lemma, so this is the closest match.

### [`odd_one`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Ring/Parity.lean#L119-L120) — `mathlib-0726`

Snippet: `samples/mathlib/mathlib-0726.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: odd_two_mul_add_one
- **file**: Mathlib/Algebra/Ring/Parity.lean
- **derivation**: by simpa only [mul_zero, zero_add] using odd_two_mul_add_one (0 : α)
- **explanation**: `odd_two_mul_add_one (a : α) : Odd (2 * a + 1)` is proved independently by `⟨_, rfl⟩`; it doesn't depend on `odd_one`. Instantiating it at `a = 0` and rewriting `2 * 0 + 1` to `1` with `mul_zero` and `zero_add` gives `Odd (1 : α)`. I found no other lemma stating `Odd 1` for a semiring. The other hits in Mathlib only use `odd_one`, and none of them state it.

### [`Set.inter_nonempty_iff_exists_right`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Set/Basic.lean#L407-L408) — `mathlib-0733`

Snippet: `samples/mathlib/mathlib-0733.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.inter_nonempty_iff_exists_left
- **file**: Mathlib/Data/Set/Basic.lean
- **derivation**: by rw [inter_comm, inter_nonempty_iff_exists_left]
- **explanation**: The sibling lemma `Set.inter_nonempty_iff_exists_left` states `(s ∩ t).Nonempty ↔ ∃ x ∈ s, x ∈ t`. The target is the same statement with `s` and `t` swapped. Rewriting with `inter_comm` turns `(s ∩ t)` into `(t ∩ s)`, and the left lemma then closes the goal. I found no other declaration that matches. `Set.inter_nonempty` has the existential form `∃ x, x ∈ s ∧ x ∈ t`, which is not the target's form. The `Finset` lemmas such as `not_disjoint_iff` are about `Finset`, not `Set`. This match is weak: it is a direct sibling in the same file, and a reviewer could reasonably treat it as `none_found` instead.

### [`Subgroup.closure_toSubmonoid_of_finite`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/GroupTheory/OrderOfElement.lean#L1162-L1168) — `mathlib-0737`

Snippet: `samples/mathlib/mathlib-0737.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.closure_toSubmonoid_of_isOfFinOrder
- **file**: Mathlib/GroupTheory/OrderOfElement.lean
- **derivation**: closure_toSubmonoid_of_isOfFinOrder <| by simp [isOfFinOrder_of_finite]
- **proof_uses_it**: True
- **explanation**: Subgroup.closure_toSubmonoid_of_isOfFinOrder (line 872) states (closure s).toSubmonoid = Submonoid.closure s for any set s whose elements all have finite order. In a finite group every element has finite order (isOfFinOrder_of_finite), so the target theorem is the special case with that hypothesis discharged. The current proof is exactly this one-line derivation. The lemma is a separate declaration, and its proof does not depend on the target. The docstring on the target also points to it.

### [`EisensteinSeries.gammaSet_one_eq`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/NumberTheory/ModularForms/EisensteinSeries/Defs.lean#L56-L59) — `mathlib-0742`

Snippet: `samples/mathlib/mathlib-0742.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: EisensteinSeries.gammaSet_one_mem_iff
- **file**: Mathlib/NumberTheory/ModularForms/EisensteinSeries/Defs.lean
- **derivation**: by obtain rfl := Subsingleton.eq_zero a; exact Set.ext fun v => gammaSet_one_mem_iff r v
- **explanation**: `gammaSet_one_mem_iff` (line 61) says `v ∈ gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r`. This is the pointwise form of the target at `a = 0`. Since `Fin 2 → ZMod 1` is a subsingleton, any `a` equals `0`, so set extensionality gives the target. The current proof is a separate `simp` call that does not use this lemma, and `gammaSet_one_mem_iff` is proved by `simp` independently of the target, so there is no circularity. The two lemmas are essentially sibling restatements of the same fact in one Mathlib file. I found no other match in Mathlib, Batteries or core.

### [`Rack.invAct_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Quandle.lean#L198-L200) — `mathlib-0749`

Snippet: `samples/mathlib/mathlib-0749.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Rack.act'_symm_apply
- **file**: Mathlib/Algebra/Quandle.lean
- **derivation**: by rw [Equiv.Perm.inv_def]; exact act'_symm_apply x y
- **explanation**: The theorem says (act' x)⁻¹ y = x ◃⁻¹ y, with the inverse taken in Equiv.Perm R. Rack.act'_symm_apply, a separate declaration in the same file, says (act' x).symm y = x ◃⁻¹ y. Equiv.Perm.inv_def (Mathlib/Algebra/Group/End.lean) says f⁻¹ = f.symm, so the two statements differ only by that rewrite. Both are proved by `rfl`. The content sits in the definition of `act'`, so there is no independent general result in Mathlib beyond these library-local lemmas. I searched Quandle.lean and Equiv.Perm.inv_def, and found no other candidate.

### [`IsMinOn.sup`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Filter/Extr.lean#L511-L512) — `mathlib-0753`

Snippet: `samples/mathlib/mathlib-0753.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsMinFilter.sup
- **file**: Mathlib/Order/Filter/Extr.lean
- **derivation**: IsMinFilter.sup hf hg
- **proof_uses_it**: True
- **explanation**: IsMinOn f s a is by definition IsMinFilter f (𝓟 s) a. IsMinFilter.sup (line 501 of the same file) is the same statement for an arbitrary filter l, so IsMinOn.sup is the case l := 𝓟 s. The current proof is that one application, which typechecks by unfolding IsMinOn. IsMinFilter.sup's proof uses bicomp_mono and sup_le_sup, not IsMinOn.sup, so it is independent.

### [`MeasureTheory.integrableOn_finset_iUnion`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Integral/IntegrableOn.lean#L233-L236) — `mathlib-0756`

Snippet: `samples/mathlib/mathlib-0756.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.integrableOn_finite_biUnion
- **file**: Mathlib/MeasureTheory/Integral/IntegrableOn.lean
- **derivation**: integrableOn_finite_biUnion s.finite_toSet
- **proof_uses_it**: True
- **explanation**: `integrableOn_finite_biUnion` has the same statement for a finite set `s : Set β` with `hs : s.Finite`. The target is that lemma with `s` replaced by the coerced Finset, using `s.finite_toSet`. The existing proof is this one-line application. I checked the statement of `integrableOn_finite_biUnion` in the same file, and it does not depend on the target.

### [`Units.mul_inv'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/GroupWithZero/Units/Basic.lean#L226-L227) — `mathlib-0758`

Snippet: `samples/mathlib/mathlib-0758.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: mul_inv_cancel₀
- **file**: Mathlib/Algebra/GroupWithZero/Defs.lean
- **derivation**: mul_inv_cancel₀ u.ne_zero
- **proof_uses_it**: True
- **explanation**: `mul_inv_cancel₀ (h : a ≠ 0) : a * a⁻¹ = 1` holds in any `MulZeroClass` group with zero. Taking `a := (u : G₀)` and `h := u.ne_zero` gives `Units.mul_inv'`. The theorem is that one-line instantiation. The existing proof is already exactly this. I found no other lemma stating `u * (u : G₀)⁻¹ = 1`; `Units.mul_inv` is about the unit inverse `↑u⁻¹`, not `(↑u)⁻¹`.

### [`TopRep.id_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RepresentationTheory/Continuous/TopRep.lean#L115-L115) — `mathlib-0766`

Snippet: `samples/mathlib/mathlib-0766.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CategoryTheory.id_apply
- **file**: Mathlib/CategoryTheory/ConcreteCategory/Basic.lean
- **derivation**: CategoryTheory.id_apply a
- **explanation**: `CategoryTheory.id_apply {X : C} (x : ToType X) : 𝟙 X x = x` is stated for any `ConcreteCategory C FC`. `TopRep k G` has such an instance, declared in this same file. The target `(𝟙 A : A ⟶ A) a = a` is that statement at `C = TopRep k G`. The coercion in the target is the concrete-category coercion, and the file's own comment says these lemmas duplicate the `ConcreteCategory` simp lemmas. The current proof is `rfl`. The match is an instance of a general lemma, with the category as the only argument fixed. I did not check how `a : A` unifies with `ToType A`. The underlying `ConcreteCategory.id_apply` field is also available.

### [`AlternatingMap.map_update_neg`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Alternating/Basic.lean#L166-L169) — `mathlib-0774`

Snippet: `samples/mathlib/mathlib-0774.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MultilinearMap.map_update_neg
- **file**: Mathlib/LinearAlgebra/Multilinear/Basic.lean
- **derivation**: g'.toMultilinearMap.map_update_neg v' i x
- **proof_uses_it**: True
- **explanation**: The theorem is the alternating-map version of `MultilinearMap.map_update_neg`. An alternating map coerces to a multilinear map through `toMultilinearMap`, and the two coercions to functions agree. Applying the multilinear lemma to `g'.toMultilinearMap` gives the statement, and that one-line application is the library's current proof. I read the multilinear lemma's statement at line 1313 of the Multilinear file. It is independent of the target, since its proof uses only `MultilinearMap.map_update_add` and `map_coord_zero`.

### [`toZ_inj`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/SuccPred/LinearLocallyFinite.lean#L327-L329) — `mathlib-0775`

Snippet: `samples/mathlib/mathlib-0775.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: injective_toZ
- **file**: Mathlib/Order/SuccPred/LinearLocallyFinite.lean
- **derivation**: injective_toZ.eq_iff
- **proof_uses_it**: True
- **explanation**: The only related declaration I found is `injective_toZ : Function.Injective (toZ i0)`, in the same file at line 307. `toZ_inj` is its `eq_iff` form, and the existing proof is `injective_toZ.eq_iff`. `injective_toZ` is a separate declaration, so this isn't circular. I grepped Mathlib for `toZ_inj`, `injective_toZ` and `toZ_injective` and found no other statement of this result.

### [`Set.inter_mul_subset`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/Pointwise/Set/Basic.lean#L388-L390) — `mathlib-0777`

Snippet: `samples/mathlib/mathlib-0777.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.image2_inter_subset_left
- **file**: Mathlib/Data/Set/NAry.lean
- **derivation**: image2_inter_subset_left
- **proof_uses_it**: True
- **explanation**: Set.image2_inter_subset_left says image2 f (s ∩ s') t ⊆ image2 f s t ∩ image2 f s' t. Set multiplication s * t is defined as image2 (· * ·) s t, so the target is that lemma with f = (· * ·), and the two sides agree by unfolding the definition. The current proof is that lemma applied directly. Analogues such as Set.inter_smul_subset prove their results the same way.

### [`Finset.cons_sdiff_cons`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Finset/SDiff.lean#L190-L190) — `mathlib-0778`

Snippet: `samples/mathlib/mathlib-0778.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.insert_sdiff_insert'
- **file**: Mathlib/Data/Finset/SDiff.lean
- **derivation**: by simpa only [cons_eq_insert] using insert_sdiff_insert' hab ha
- **explanation**: `Finset.insert_sdiff_insert'` (hab : a ≠ b) (ha : a ∉ s) : insert a s \ insert b s = {a} is the same statement for `insert`. `Finset.cons a s ha` equals `insert a s` by `cons_eq_insert`, so rewriting with it gives the target. The `hb` argument is not needed, so the Mathlib lemma is slightly stronger. Its proof (`ext; aesop`) does not depend on `cons_sdiff_cons`. The current proof uses `grind` instead.

### [`FiniteMulArchimedeanClass.mem_closedBallSubgroup_iff`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Archimedean/Class.lean#L908-L911) — `mathlib-0779`

Snippet: `samples/mathlib/mathlib-0779.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FiniteMulArchimedeanClass.mem_subgroup_iff
- **file**: Mathlib/Algebra/Order/Archimedean/Class.lean
- **derivation**: by simpa using mem_subgroup_iff (s := UpperSet.Ici c) (a := a)
- **proof_uses_it**: True
- **explanation**: closedBallSubgroup c is an abbrev for subgroup (UpperSet.Ici c). mem_subgroup_iff says a ∈ subgroup s ↔ ∀ h : a ≠ 1, mk a h ∈ s. Taking s = UpperSet.Ici c and rewriting membership with UpperSet.mem_Ici_iff gives the target. The current proof is `simp`, which uses the simp lemma mem_subgroup_iff. The MulArchimedeanClass version of this lemma is for a different type, so it isn't a match. I found no other declaration with this statement.

### [`Filter.EventuallyLE.rfl`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Filter/Basic.lean#L1217-L1218) — `mathlib-0780`

Snippet: `samples/mathlib/mathlib-0780.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Filter.EventuallyLE.refl
- **file**: Mathlib/Order/Filter/Basic.lean
- **derivation**: EventuallyLE.refl l f
- **proof_uses_it**: True
- **explanation**: `Filter.EventuallyLE.refl (l : Filter α) (f : α → β) : f ≤ᶠ[l] f` (same Preorder setting, line 1214) is the same statement with explicit rather than implicit arguments. It is proved independently, via `EventuallyEq.rfl.le`, so it doesn't depend on `EventuallyLE.rfl`. The theorem's own proof is exactly `EventuallyLE.refl l f`.

### [`IsMinFilter.filter_mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Filter/Extr.lean#L251-L252) — `mathlib-0782`

Snippet: `samples/mathlib/mathlib-0782.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Filter.Eventually.filter_mono
- **file**: Mathlib/Order/Filter/Basic.lean
- **derivation**: Filter.Eventually.filter_mono hl h
- **explanation**: IsMinFilter f l a is by definition `∀ᶠ x in l, f a ≤ f x`. Filter.Eventually.filter_mono (h : f₁ ≤ f₂) (hp : ∀ᶠ x in f₂, p x) : ∀ᶠ x in f₁, p x, instantiated with p := fun x => f a ≤ f x, gives the claim after unfolding IsMinFilter. The current proof `hl h` uses filter order directly, which is the same term as Eventually.filter_mono's proof.

### [`Fin.image_succ_Ioo`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Interval/Set/Fin.lean#L779-L780) — `mathlib-0784`

Snippet: `samples/mathlib/mathlib-0784.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Fin.image_addNat_Ioo
- **file**: Mathlib/Order/Interval/Set/Fin.lean
- **derivation**: image_addNat_Ioo 1 i j
- **proof_uses_it**: True
- **explanation**: `Fin.image_addNat_Ioo m i j` says `(addNat · m) '' Ioo i j = Ioo (i.addNat m) (j.addNat m)`, and it is a separate declaration from the target. Take `m = 1` and `succ i` is definitionally `i.addNat 1`, which gives `Fin.image_succ_Ioo`. That is why the existing proof is just `image_addNat_Ioo ..`. I read the statement at line 685 of the same file. I found no more general Mathlib lemma. Mathlib has no `Fin.succ` image lemma for `Ioo` outside this file. The only other matches are the sibling lemmas for `Icc` and `Ico`, and `finsetImage_succ_Ioo` for `Finset`.

### [`mulLeft_continuous`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Algebra/Ring/Basic.lean#L387-L389) — `mathlib-0793`

Snippet: `samples/mathlib/mathlib-0793.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: continuous_const_mul
- **file**: Mathlib/Topology/Algebra/Monoid/Defs.lean
- **derivation**: continuous_const_mul x
- **explanation**: `continuous_const_mul (m : M) : Continuous (m * ·)` holds for any `ContinuousMul`/separately continuous multiplication, which `IsSemitopologicalRing` provides. The coercion of `AddMonoidHom.mulLeft x` unfolds definitionally to `fun y => x * y`, so the statement is the same after unfolding. Mathlib already relies on this: `Mathlib/Topology/Algebra/Nonarchimedean/Basic.lean:123` uses `continuous_const_mul r` as a proof of `Continuous (AddMonoidHom.mulLeft r)`. The current proof, `continuous_id.const_mul _`, uses the closely related `Continuous.const_mul`, which is itself proved from `continuous_const_mul`.

### [`CircleDeg1Lift.mono`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Dynamics/Circle/RotationNumber/TranslationNumber.lean#L150-L150) — `mathlib-0794`

Snippet: `samples/mathlib/mathlib-0794.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: OrderHomClass.mono
- **file**: Mathlib/Order/Hom/Basic.lean
- **derivation**: OrderHomClass.mono f h
- **explanation**: CircleDeg1Lift has an `OrderHomClass CircleDeg1Lift ℝ ℝ` instance (line 139 of the same file, built from `toOrderHom`, not from `mono`). `OrderHomClass.mono (f : F) : Monotone f` (also tagged `@[gcongr]`) gives `x ≤ y → f x ≤ f y` directly. The current proof uses `f.monotone`, which is the local `CircleDeg1Lift.monotone`. The statement is the general monotonicity of order-hom-class maps, applied to `CircleDeg1Lift`.

### [`IsNonarchimedean.add_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Ring/IsNonarchimedean.lean#L25-L30) — `mathlib-0799`

Snippet: `samples/mathlib/mathlib-0799.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: max_le_add_of_nonneg
- **file**: Mathlib/Algebra/Order/Monoid/Unbundled/MinMax.lean
- **derivation**: exact (hna _ _).trans (max_le_add_of_nonneg (f_nonneg _) (f_nonneg _))
- **explanation**: `max_le_add_of_nonneg` is the additive version of `max_le_mul_of_one_le`. It states `0 ≤ a → 0 ≤ b → max a b ≤ a + b` for `[AddLeftMono α] [AddRightMono α]`. The ordered semiring `R` has both instances. `IsNonarchimedean f` unfolds to `f (a + b) ≤ f a ⊔ f b`, and `⊔` is `max` on a linear order. The theorem is therefore `hna a b` followed by `max_le_add_of_nonneg` applied to `f_nonneg a` and `f_nonneg b`. Mathlib already uses this lemma for the same triangle inequality in `NormedValued.lean` and `PadicNorm.lean`. I did not find a lemma that states `IsNonarchimedean.add_le` itself. The other `add_le` hits I found (e.g. `FinitePlace.add_le`) are different declarations.

### [`FiniteArchimedeanClass.mem_ball_iff`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Module/Archimedean.lean#L83-L86) — `mathlib-0802`

Snippet: `samples/mathlib/mathlib-0802.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FiniteArchimedeanClass.mem_ballAddSubgroup_iff
- **file**: Mathlib/Algebra/Order/Archimedean/Class.lean
- **derivation**: mem_ballAddSubgroup_iff
- **proof_uses_it**: True
- **explanation**: The additive version of `FiniteMulArchimedeanClass.mem_ballSubgroup_iff` states `a ∈ ballAddSubgroup c ↔ ∀ h : a ≠ 0, c < mk a h`. The theorem here states the same membership for the submodule `ball K c`. That submodule has the same carrier as `ballAddSubgroup c`, and `toAddSubgroup_ball` is `rfl`. So the subgroup lemma proves the theorem by unfolding the definitions, and the current proof is exactly that one line. The theorem is a restatement for the submodule version of the ball. I found no other Mathlib declaration that states it for submodules.

### [`Set.iInter_div_subset`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Group/Pointwise/Set/Lattice.lean#L166-L168) — `mathlib-0804`

Snippet: `samples/mathlib/mathlib-0804.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.image2_iInter_subset_left
- **file**: Mathlib/Data/Set/Lattice/Image.lean
- **derivation**: image2_iInter_subset_left ..
- **proof_uses_it**: True
- **explanation**: Set.image2_iInter_subset_left states image2 f (⋂ i, s i) t ⊆ ⋂ i, image2 f (s i) t. Pointwise division on sets is image2 (· / ·), so the target is this lemma with f := (· / ·). The current proof is exactly that one-line application.

### [`LeftInvariantDerivation.left_invariant`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Geometry/Manifold/Algebra/LeftInvariantDerivation.lean#L202-L203) — `mathlib-0808`

Snippet: `samples/mathlib/mathlib-0808.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: LeftInvariantDerivation.left_invariant'
- **file**: Mathlib/Geometry/Manifold/Algebra/LeftInvariantDerivation.lean
- **derivation**: left_invariant' g X
- **explanation**: `LeftInvariantDerivation.left_invariant'` (line 93, same file) states `𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt (1 : G) ↑X) = Derivation.evalAt g ↑X`. The target theorem states the same with `evalAt (1:G) X`, where the coercion to `Derivation` is inserted automatically. The only difference is the explicit/implicit argument pattern. Both are proved directly from the structure field `left_invariant''`, so neither depends on the other. The docstring calls `left_invariant'` a "premature version" of the target. The target's own proof uses the field `left_invariant''`, not `left_invariant'`. I did not search outside this file.

### [`LocallyConstant.mulIndicator_of_notMem`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/LocallyConstant/Basic.lean#L476-L478) — `mathlib-0817`

Snippet: `samples/mathlib/mathlib-0817.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.mulIndicator_of_notMem
- **file**: Mathlib/Algebra/Group/Indicator.lean
- **derivation**: Set.mulIndicator_of_notMem h _
- **proof_uses_it**: True
- **explanation**: The proof is exactly `Set.mulIndicator_of_notMem h _`. `LocallyConstant.mulIndicator f hU` is defined with `toFun := Set.mulIndicator U f`. So the target is Mathlib's lemma `a ∉ s → mulIndicator s f a = 1` after unfolding that definition. I did not open the file for Set.mulIndicator_of_notMem. The path is my recollection of where it lives, and the name comes from the in-file proof.

### [`Semigroup.exists_finite_of_isMulFG`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/GroupTheory/Finiteness.lean#L138-L141) — `mathlib-0818`

Snippet: `samples/mathlib/mathlib-0818.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Semigroup.isMulFG_iff_finite
- **file**: Mathlib/GroupTheory/Finiteness.lean
- **derivation**: Semigroup.isMulFG_iff_finite.mp ‹_›
- **proof_uses_it**: True
- **explanation**: Semigroup.isMulFG_iff_finite (line 135) states IsMulFG M ↔ ∃ S : Set M, S.Finite ∧ Subsemigroup.closure S = ⊤. The theorem is its forward direction, applied to the instance argument. This is `.mp` glue, and the current proof is exactly this. The iff is a different declaration, proved by `rw [isMulFG_iff, ← Finset.exists_toSet]` and independent of the theorem. I only read the neighbouring declarations in this file and did not search the rest of Mathlib.

### [`InformationTheory.klDiv_ne_top`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/InformationTheory/KullbackLeibler/Basic.lean#L102-L103) — `mathlib-0825`

Snippet: `samples/mathlib/mathlib-0825.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: InformationTheory.klDiv_ne_top_iff
- **file**: Mathlib/InformationTheory/KullbackLeibler/Basic.lean
- **derivation**: klDiv_ne_top_iff.mpr ⟨hμν, h_int⟩
- **proof_uses_it**: True
- **explanation**: klDiv_ne_top_iff states `klDiv μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ`, which is a different declaration in the same file. The target is its reverse direction, with the conjunction curried. The target's proof is `klDiv_ne_top_iff.mpr ⟨hμν, h_int⟩`. That iff is proved from klDiv_eq_top_iff via simp, so it does not depend on the target. I found no other declaration with this statement.

### [`ProbabilityTheory.CondIndep.condIndepSets`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Probability/Independence/Conditional.lean#L526-L529) — `mathlib-0829`

Snippet: `samples/mathlib/mathlib-0829.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ProbabilityTheory.Kernel.Indep.indepSets
- **file**: Mathlib/Probability/Independence/Kernel/Indep.lean
- **derivation**: Kernel.Indep.indepSets h_indep
- **proof_uses_it**: True
- **explanation**: CondIndep m' m₁ m₂ hm' μ is by definition Kernel.Indep m₁ m₂ (condExpKernel μ m') (μ.trim hm'), and CondIndepSets m' hm' s1 s2 μ is Kernel.IndepSets s1 s2 (condExpKernel μ m') (μ.trim hm'). So the theorem is Kernel.Indep.indepSets (statement: Indep (generateFrom s1) (generateFrom s2) κ μ → IndepSets s1 s2 κ μ) with κ := condExpKernel μ m' and μ := μ.trim hm'. The current proof is exactly that one application, after unfolding the two definitions.

### [`Polynomial.hasFDerivWithinAt_aeval`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/Deriv/Polynomial.lean#L137-L140) — `mathlib-0831`

Snippet: `samples/mathlib/mathlib-0831.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.hasFDerivAt_aeval
- **file**: Mathlib/Analysis/Calculus/Deriv/Polynomial.lean
- **derivation**: (q.hasFDerivAt_aeval x).hasFDerivWithinAt
- **proof_uses_it**: True
- **explanation**: The theorem is the HasFDerivWithinAt version of the sibling declaration Polynomial.hasFDerivAt_aeval, which has the same function and the same derivative, smulRight 1 (aeval x (derivative q)), but for HasFDerivAt. Applying the generic HasFDerivAt.hasFDerivWithinAt gives the target in one line, and the current proof does exactly that. I searched the repository for other `hasFDerivWithinAt_aeval` and `hasFDerivAt_aeval` declarations and found none besides these two.

### [`Set.insert_Icc_left_eq_Icc_sub_one`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Order/Interval/Set/SuccPred.lean#L152-L154) — `mathlib-0833`

Snippet: `samples/mathlib/mathlib-0833.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.insert_Icc_left_eq_Icc_pred
- **file**: Mathlib/Order/Interval/Set/SuccPred.lean
- **derivation**: by simpa [← pred_eq_sub_one] using Set.insert_Icc_left_eq_Icc_pred (pred_eq_sub_one a ▸ h)
- **proof_uses_it**: True
- **explanation**: The general lemma `Set.insert_Icc_left_eq_Icc_pred` (in `Mathlib/Order/Interval/Set/SuccPred.lean`, `@[to_dual]` of `insert_Icc_pred_right_eq_Icc`) states `pred a ≤ b → insert (pred a) (Icc a b) = Icc (pred a) b` for a `PredOrder`. The target is the same statement with `pred a` replaced by `a - 1`. The two are linked by `pred_eq_sub_one` in a `PredSubOrder`, so the proof is just a rewrite plus that lemma. This is the library's own wrapper, and the lemma it wraps is independent of it. The Finset analogue in `Mathlib/Algebra/Order/Interval/Finset/SuccPred.lean` has the same name but is about `Finset`, so it is a different statement. I found no other Set-level statement of this result in the Mathlib sources I searched.

### [`MDifferentiableAt.neg`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean#L947-L948) — `mathlib-0844`

Snippet: `samples/mathlib/mathlib-0844.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MDifferentiableWithinAt.neg
- **file**: Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean
- **derivation**: mdifferentiableWithinAt_univ.mp (hf.mdifferentiableWithinAt (s := univ)).neg
- **explanation**: `MDifferentiableWithinAt.neg` (line 944, same file) states the same result for `MDiffAt[s] f z`. It follows from the within-set version with `s = univ`. The glue is `mdifferentiableWithinAt_univ` and `MDifferentiableAt.mdifferentiableWithinAt`, both in MFDeriv/Basic.lean. The within version's proof goes through `HasMFDerivWithinAt.neg`, not `MDifferentiableAt.neg`, so it is independent of the target. The target's own proof uses `HasMFDerivAt.neg` instead. `mdifferentiableAt_neg` (an iff, same file) matches too, but its proof calls `MDifferentiableAt.neg`, so it is circular and I did not use it. I did not find a separate match elsewhere: `mdifferentiableAt_neg_section` in VectorBundle/MDifferentiable.lean is about bundle sections, not functions into a normed space.

### [`Sum.inl_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Sum/Basic.lean#L42-L42) — `mathlib-0845`

Snippet: `samples/mathlib/mathlib-0845.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Sum.inl.inj
- **file**: Init/Prelude.lean (auto-generated injectivity theorem for the constructor Sum.inl; see also Sum.inl.inj_iff in Init/Data/Sum/Lemmas.lean)
- **derivation**: fun _ _ ↦ Sum.inl.inj
- **proof_uses_it**: True
- **explanation**: Lean core generates `Sum.inl.inj : inl a = inl b → a = b` for the constructor `Sum.inl`. `Function.Injective inl` unfolds to exactly this statement, so it is the same result with the quantifiers made explicit. The current proof is `fun _ _ ↦ inl.inj`. I found no separately named `inl_injective` in core or Batteries. The only match is this generated lemma, which is plain constructor injectivity. The case for calling it a duplicate is therefore weaker than usual.

### [`LinearMap.toMatrix_mul`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Matrix/ToLin.lean#L764-L766) — `mathlib-0853`

Snippet: `samples/mathlib/mathlib-0853.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.toMatrix_comp
- **file**: Mathlib/LinearAlgebra/Matrix/ToLin.lean
- **derivation**: by rw [Module.End.mul_eq_comp]; exact LinearMap.toMatrix_comp v₁ v₁ v₁ f g
- **proof_uses_it**: True
- **explanation**: LinearMap.toMatrix_comp (line 758, same file) states toMatrix v₁ v₃ (f.comp g) = toMatrix v₂ v₃ f * toMatrix v₁ v₂ g for f : M₂ →ₗ M₃ and g : M₁ →ₗ M₂. Taking M₂ = M₃ = M₁ with all three bases equal to v₁ gives the target, because multiplication in M₁ →ₗ[R] M₁ is composition (Module.End.mul_eq_comp). The current proof does exactly this. I rejected LinearMap.toMatrixAlgEquiv_mul and LinearMap.toMatrix'_mul as duplicates. The first is defined using toMatrix_mul, so it is circular. The second is the case of a basis that is the standard basis only.

### [`nhdsWithin_Ici_neBot`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Order/LeftRight.lean#L49-L51) — `mathlib-0854`

Snippet: `samples/mathlib/mathlib-0854.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: nhdsWithin_neBot_of_mem
- **file**: Mathlib/Topology/NhdsWithin.lean
- **derivation**: exact nhdsWithin_neBot_of_mem H₂
- **proof_uses_it**: True
- **explanation**: `nhdsWithin_neBot_of_mem` (line 415) states `x ∈ s → NeBot (𝓝[s] x)` for any set s. The target is the instance s := Ici a, x := b. Membership `b ∈ Ici a` is defeq to `a ≤ b`, so the existing proof is a single application. I found no other lemma that states this for Ici without going through this one. The other `NeBot` lemmas I checked were the Ioi, Ico, Ioo and ≠ variants, which have different statements.

### [`Matrix.transpose_comp`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Matrix/Composition.lean#L116-L118) — `mathlib-0855`

Snippet: `samples/mathlib/mathlib-0855.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.comp_map_transpose
- **file**: Mathlib/Data/Matrix/Composition.lean
- **derivation**: by rw [comp_map_transpose, transpose_transpose]
- **explanation**: `Matrix.comp_map_transpose` (same file, line 110) says `comp I J L K R (M.map (·ᵀ)) = (comp _ _ _ _ R Mᵀ)ᵀ`, proved by `rfl` and independent of the target. Apply it with `M := Mᵀ`, which gives `comp J I L K R (Mᵀ.map (·ᵀ)) = (comp I J K L R Mᵀᵀ)ᵀ`. Then `transpose_transpose` turns the right-hand side into `(comp I J K L R M)ᵀ`, which is the target with its sides swapped. This is a single instantiation plus one rewrite, so I classed it as a special case rather than an exact duplicate. `Matrix.comp_transpose` and `Matrix.comp_symm_transpose` are close variants, but I did not check them further. I only read this one file.

### [`ENNReal.continuousAt_const_mul`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Instances/ENNReal/Lemmas.lean#L378-L380) — `mathlib-0858`

Snippet: `samples/mathlib/mathlib-0858.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ENNReal.Tendsto.const_mul
- **file**: Mathlib/Topology/Instances/ENNReal/Lemmas.lean
- **derivation**: ENNReal.Tendsto.const_mul tendsto_id h.symm
- **proof_uses_it**: True
- **explanation**: ENNReal.Tendsto.const_mul gives Tendsto (fun x => a * m x) f (𝓝 (a*b)) from Tendsto m f (𝓝 b) and (b ≠ 0 ∨ a ≠ ∞). Taking m = id and f = 𝓝 b gives ContinuousAt (a * ·) b, with the disjunction swapped by `h.symm`. The current proof is exactly this one-line instantiation. I found no other lemma with this statement.

### [`HasMFDerivAt.sum`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean#L888-L892) — `mathlib-0860`

Snippet: `samples/mathlib/mathlib-0860.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HasMFDerivWithinAt.sum
- **file**: Mathlib/Geometry/Manifold/MFDeriv/SpecificFunctions.lean
- **derivation**: by simp_all only [← hasMFDerivWithinAt_univ]; exact HasMFDerivWithinAt.sum hf
- **proof_uses_it**: True
- **explanation**: HasMFDerivWithinAt.sum (line 881 of the same file) states the sum rule for the manifold derivative within a set s. It is proved independently by Finset induction. HasMFDerivAt.sum is the case s = univ, via hasMFDerivWithinAt_univ. The current proof already does exactly this. I found no other declaration with this statement. The grep for sum-related HasMFDerivAt lemmas only turned up the within-version and the MDifferentiable variants.

### [`UpperHemicontinuousAt.inter`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Semicontinuity/Hemicontinuity.lean#L289-L294) — `mathlib-0862`

Snippet: `samples/mathlib/mathlib-0862.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: UpperHemicontinuousWithinAt.inter
- **file**: Mathlib/Topology/Semicontinuity/Hemicontinuity.lean
- **derivation**: upperHemicontinuousWithinAt_univ_iff.mp ((hf.upperHemicontinuousWithinAt univ).inter hu)
- **proof_uses_it**: True
- **explanation**: `UpperHemicontinuousWithinAt.inter` (line 274) gives the same result for `UpperHemicontinuousWithinAt f s x`. The target is the case s = univ. `upperHemicontinuousWithinAt_univ_iff` is in Defs.lean at line 848. It says `UpperHemicontinuousWithinAt f univ x ↔ UpperHemicontinuousAt f x`, which converts between the two forms. The current proof already works this way. It rewrites with that iff and then applies `hf.inter hu`. I found no other `UpperHemicontinuousAt` result elsewhere in Mathlib. The only files that mention the name are Defs.lean and Hemicontinuity.lean.

### [`ContinuousAlternatingMap.le_mul_prod_of_opNorm_le_of_le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean#L214-L217) — `mathlib-0864`

Snippet: `samples/mathlib/mathlib-0864.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le
- **file**: Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean
- **derivation**: f.1.le_mul_prod_of_opNorm_le_of_le hC hm
- **proof_uses_it**: True
- **explanation**: The multilinear lemma gives ‖f m‖ ≤ C * ∏ b i for a continuous multilinear map f, given ‖f‖ ≤ C and ‖m i‖ ≤ b i. The alternating statement is that lemma applied to the underlying multilinear map f.1. Here f.1 m is defeq to f m, and ‖f.1‖ = ‖f‖ holds by rfl (`norm_toContinuousMultilinearMap`). The library's current proof is already this one-line application. The statements are on different types, so I classed it as a special case and not a duplicate.

### [`BddOrd.inv_hom_apply`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Category/BddOrd.lean#L146-L147) — `mathlib-0866`

Snippet: `samples/mathlib/mathlib-0866.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CategoryTheory.Iso.hom_inv_id_apply
- **file**: Mathlib/CategoryTheory/Elementwise.lean
- **derivation**: Iso.hom_inv_id_apply e x
- **proof_uses_it**: True
- **explanation**: `Mathlib/CategoryTheory/Elementwise.lean` line 26 has `attribute [elementwise (attr := simp)] Iso.hom_inv_id Iso.inv_hom_id`. That generates `Iso.hom_inv_id_apply`, which says that for any concrete category `C`, an iso `f : X ≅ Y` and `x : ToType X`, `f.inv (f.hom x) = x`. `BddOrd` is a concrete category, so this is exactly `BddOrd.inv_hom_apply`. I did not read the generated statement itself. Its form comes from the `elementwise` attribute and the attribute line. Mathlib's own uses of `Iso.hom_inv_id_apply` in files such as `MayerVietoris.lean` match this form. The current proof is `simp`, which closes the goal with this `@[simp]` lemma, so the proof already uses it. I did not check whether the generated lemma carries extra universe or instance requirements.

### [`LieSubmodule.trivial_lie_oper_zero`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Algebra/Lie/Abelian.lean#L344-L348) — `mathlib-0869`

Snippet: `samples/mathlib/mathlib-0869.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LieSubmodule.lie_eq_bot_iff
- **file**: Mathlib/Algebra/Lie/IdealOperations.lean
- **derivation**: (LieSubmodule.lie_eq_bot_iff _ _).2 fun x _ m _ => trivial_lie_zero L M x m
- **explanation**: `LieSubmodule.lie_eq_bot_iff` says `⁅I, N⁆ = ⊥ ↔ ∀ x ∈ I, ∀ m ∈ N, ⁅x, m⁆ = 0`. Under `LieModule.IsTrivial L M`, every bracket `⁅x, m⁆` is `0` by `trivial_lie_zero`, so the right-hand side holds. The current proof goes through `lieIdeal_oper_eq_span` and `lieSpan_le` instead. `IdealOperations.lean` imports only `Lie.Ideal`, so it does not depend on the theorem being judged. I did not check the argument order of `lie_eq_bot_iff` or the argument order of `trivial_lie_zero` in the sources, so the derivation may need small adjustments.

### [`ConcaveOn.condExp_map_le_univ`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean#L228-L234) — `mathlib-0873`

Snippet: `samples/mathlib/mathlib-0873.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ConcaveOn.condExp_map_le
- **file**: Mathlib/MeasureTheory/Function/ConditionalExpectation/CondJensen.lean
- **derivation**: ConcaveOn.condExp_map_le hm hφ_cvx (upperSemicontinuousOn_univ_iff.2 hφ_cont) (by simp) isClosed_univ hf_int hφ_int
- **explanation**: ConcaveOn.condExp_map_le is the general conditional Jensen inequality for concave φ on a closed set s with f ∈ s a.e. and φ upper semicontinuous on s. The target is the case s = univ. Instantiating s := univ needs upperSemicontinuousOn_univ_iff, `by simp` for the a.e. membership, and isClosed_univ. This is the same pattern Mathlib uses for the convex version, ConvexOn.map_condExp_le_univ, which is proved directly from ConvexOn.map_condExp_le. The current proof of the target instead negates φ and uses ConvexOn.map_condExp_le_univ, so it does not use the candidate. The candidate's own proof (negate, then ConvexOn.map_condExp_le) does not depend on the target, so the candidate is independent.

### [`Prod.range_snd`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Set/Image.lean#L761-L763) — `mathlib-0876`

Snippet: `samples/mathlib/mathlib-0876.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Function.Surjective.range_eq
- **file**: Mathlib/Data/Set/Image.lean
- **derivation**: Prod.snd_surjective.range_eq
- **proof_uses_it**: True
- **explanation**: Function.Surjective.range_eq (an alias of Set.range_eq_univ.mpr) says Surjective f → range f = univ. Prod.range_snd is that statement with f := Prod.snd. The surjectivity is supplied by Prod.snd_surjective, which needs [Nonempty α]. The library's proof is exactly this one-line application. I found no other Mathlib declaration stating the Set-level fact for Prod.snd. The other `range_snd` lemmas I saw are about subrings, linear maps and schemes.

### [`Ordinal.le_omega_self`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/SetTheory/Cardinal/Aleph.lean#L236-L237) — `mathlib-0889`

Snippet: `samples/mathlib/mathlib-0889.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: StrictMono.le_apply
- **file**: Mathlib/Order/WellFounded.lean
- **derivation**: omega_strictMono.le_apply
- **proof_uses_it**: True
- **explanation**: `StrictMono.le_apply` says that a strictly monotone self-map f of a well-founded linear order satisfies x ≤ f x. The theorem is this lemma with f := Ordinal.omega on Ordinal, with `omega_strictMono` supplying the hypothesis. The current proof is exactly this one-line application. I found no other lemma in Mathlib, Batteries or core stating o ≤ ω_ o. For example, there is no `le_aleph_self`.

### [`Fin.castAdd_inj`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Fin/SuccPred.lean#L86-L86) — `mathlib-0890`

Snippet: `samples/mathlib/mathlib-0890.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Fin.castAdd_injective
- **file**: Mathlib/Data/Fin/SuccPred.lean
- **derivation**: (Fin.castAdd_injective _ _).eq_iff
- **explanation**: `Fin.castAdd_injective m n : Injective (@Fin.castAdd m n)` is the injectivity form of this statement. `Function.Injective.eq_iff` turns it into `castAdd n a = castAdd n b ↔ a = b`, which is `castAdd_inj`. The proof of `castAdd_injective` goes through `castLE_injective`, so it doesn't depend on the target. The ↔ form with an implicit `hmn` also appears as `Fin.castLE_inj`. `castAdd n` unfolds definitionally to `castLE (Nat.le_add_right _ _)`, so `castLE_inj` would also work. The core lemma `Fin.castSucc_inj` is the analogue for `castSucc`, not for `castAdd`. I searched Mathlib, Batteries and Lean core for `castAdd_inj*` and `castLE_inj*` and found no other candidates.

### [`deriv_const_sub'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/Calculus/Deriv/Add.lean#L445-L447) — `mathlib-0892`

Snippet: `samples/mathlib/mathlib-0892.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: deriv_const_sub
- **file**: Mathlib/Analysis/Calculus/Deriv/Add.lean
- **derivation**: funext fun _ => deriv_const_sub c
- **proof_uses_it**: True
- **explanation**: `deriv_const_sub` (line 442) states `deriv (c - f ·) x = -deriv f x` for a fixed `x`. The target is its function-level form, obtained by `funext`, which is routine glue. The current proof is exactly that. I also found `deriv_const_sub_id` and `deriv_const_sub_id'`. They are specialised to `id` and don't match. I found no other declaration with the function-level statement.

### [`IsLocalization.subsingleton_iff`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/Localization/Defs.lean#L220-L221) — `mathlib-0896`

Snippet: `samples/mathlib/mathlib-0896.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submonoid.LocalizationMap.subsingleton_iff
- **file**: Mathlib/GroupTheory/MonoidLocalization/MonoidWithZero.lean
- **derivation**: (toLocalizationMap M S).subsingleton_iff
- **proof_uses_it**: True
- **explanation**: `Submonoid.LocalizationMap.subsingleton_iff` states `Subsingleton N ↔ 0 ∈ S` for any monoid localization map `f : LocalizationMap S N` of commutative monoids with zero. `IsLocalization.subsingleton_iff` is the ring version. It applies the general lemma to `IsLocalization.toLocalizationMap M S`, which is the localization map built from the `IsLocalization M S` instance. The current proof is exactly that one-line instantiation. I found no other declaration with this statement. `OreLocalization.subsingleton_iff` is about a different type.

### [`Finset.exists_notMem`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Set/Finite/Basic.lean#L857-L857) — `mathlib-0901`

Snippet: `samples/mathlib/mathlib-0901.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Infinite.exists_notMem_finset
- **file**: Mathlib/Data/Fintype/EquivFin.lean
- **derivation**: Infinite.exists_notMem_finset s
- **explanation**: `Infinite.exists_notMem_finset [Infinite α] (s : Finset α) : ∃ x, x ∉ s` has exactly the same statement as `Finset.exists_notMem`. Only the name differs. Its proof is `not_forall.1 fun h => Fintype.false ⟨s, h⟩`. That proof doesn't depend on the target: the target's own proof goes through `Set.Finite.exists_notMem`, and the Data/Fintype/EquivFin.lean declaration is separate from it. The library's current proof uses `s.finite_toSet.exists_notMem` instead.

### [`affineSpan_nonempty`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean#L1027-L1029) — `mathlib-0905`

Snippet: `samples/mathlib/mathlib-0905.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: spanPoints_nonempty
- **file**: Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean
- **derivation**: spanPoints_nonempty k s
- **proof_uses_it**: True
- **explanation**: `spanPoints_nonempty k s : (spanPoints k s).Nonempty ↔ s.Nonempty` (line 123) is proved independently, before affineSpan is defined. The carrier of `affineSpan k s` is definitionally `spanPoints k s`, so the target is that lemma after unfolding `affineSpan`. The target's proof is exactly this term. I found no other independent match: the other uses (`affineSpan_eq_bot`, `Set.Nonempty.affineSpan`) are consequences of the target or aliases of it.

### [`ringKrullDim_eq_bot_of_subsingleton`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/KrullDimension/Basic.lean#L43-L45) — `mathlib-0909`

Snippet: `samples/mathlib/mathlib-0909.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Order.krullDim_eq_bot
- **file**: Mathlib/Order/KrullDimension.lean
- **derivation**: krullDim_eq_bot
- **proof_uses_it**: True
- **explanation**: `ringKrullDim R` unfolds to `krullDim (PrimeSpectrum R)`. `Order.krullDim_eq_bot [IsEmpty α] : krullDim α = ⊥` applies with α := PrimeSpectrum R, since a subsingleton semiring has an empty prime spectrum (the instance is found automatically). The current proof is exactly this one-line instantiation. Alternatively, `ringKrullDim_eq_bot_iff_subsingleton.mpr ‹_›` also works. That lemma is in the same file, and its proof does not use the target.

### [`ConnectedComponents.isQuotientMap_coe`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Connected/Clopen.lean#L531-L532) — `mathlib-0912`

Snippet: `samples/mathlib/mathlib-0912.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: isQuotientMap_quot_mk
- **file**: Mathlib/Topology/Constructions.lean
- **derivation**: isQuotientMap_quot_mk
- **proof_uses_it**: True
- **explanation**: ConnectedComponents α is the quotient of α by the setoid connectedComponentSetoid, with the quotient topology, and `mk` is the quotient map. Mathlib's `isQuotientMap_quot_mk` (and `isQuotientMap_quotient_mk'` for Setoid quotients) says `Quot.mk` is a quotient map for any relation. The target statement is that lemma with the relation set to connectedComponent equivalence. It holds by unfolding definitions, which is how the current proof works. I did not find a separate ConnectedComponents-specific duplicate in Mathlib.

### [`Multiset.induction_on`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Multiset/ZeroCons.lean#L120-L123) — `mathlib-0915`

Snippet: `samples/mathlib/mathlib-0915.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Multiset.induction
- **file**: Mathlib/Data/Multiset/ZeroCons.lean
- **derivation**: Multiset.induction empty cons s
- **proof_uses_it**: True
- **explanation**: `Multiset.induction` (line 116 of the same file) states `p 0 → (∀ a s, p s → p (a ::ₘ s)) → ∀ s, p s`. `Multiset.induction_on` is the same statement with `s` moved to the front, so the two differ only in argument order. `induction_on` is proved by applying `Multiset.induction` directly. `Multiset.induction` is proved independently, by `rintro ⟨l⟩` and list induction, so there is no circularity.

### [`biSup_prod'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/CompleteLattice/Basic.lean#L702-L705) — `mathlib-0926`

Snippet: `samples/mathlib/mathlib-0926.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: biSup_prod
- **file**: Mathlib/Order/CompleteLattice/Basic.lean
- **derivation**: biSup_prod (f := fun x => f x.1 x.2)
- **proof_uses_it**: True
- **explanation**: `biSup_prod` states `⨆ x ∈ s ×ˢ t, f x = ⨆ (a ∈ s) (b ∈ t), f (a, b)` for `f : β × γ → α`. Taking `f := fun x => f x.1 x.2` gives the target, because `(a, b).1 = a` and `(a, b).2 = b` hold by definitional unfolding. The current proof is exactly `biSup_prod`. `biSup_prod'` is the curried-function form of `biSup_prod`. It is a distinct declaration, and `biSup_prod` is proved independently via `iSup_prod`.

### [`Projectivization.Subspace.span_iUnion`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Projectivization/Subspace.lean#L184-L187) — `mathlib-0928`

Snippet: `samples/mathlib/mathlib-0928.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: GaloisConnection.l_iSup
- **file**: Mathlib/Order/GaloisConnection/Basic.lean
- **derivation**: (@gi K V _ _ _).gc.l_iSup
- **proof_uses_it**: True
- **explanation**: The lower adjoint of any Galois connection between complete lattices preserves arbitrary suprema: l (iSup f) = ⨆ i, l (f i). Here l = span, from the Galois insertion Projectivization.Subspace.gi between Set (ℙ K V) and Subspace K V. The set iSup is ⋃ definitionally. This is exactly the library's existing one-line proof. Searching found no other Mathlib declaration stating span_iUnion for projective subspaces.

### [`CategoryTheory.Functor.curry_obj_injective`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Functor/Currying.lean#L169-L171) — `mathlib-0931`

Snippet: `samples/mathlib/mathlib-0931.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Functor.curryingEquiv
- **file**: Mathlib/CategoryTheory/Functor/Currying.lean
- **derivation**: exact curryingEquiv.symm.injective h
- **explanation**: `curryingEquiv : (C ⥤ D ⥤ E) ≃ (C × D ⥤ E)` has `invFun G := curry.obj G` and `right_inv := uncurry_obj_curry_obj`. It was not built from the target lemma. So `curryingEquiv.symm.injective h` gives the target's statement. `curryingEquiv.symm` unfolds definitionally to `curry.obj`. The remaining step is the generic `Equiv.injective`. The only other injectivity statement found for a currying construction in CategoryTheory is `curry_injective` in `Monoidal/Closed/Basic.lean`, and that one is about morphisms in a monoidal closed category. It is not a match.

### [`GroupFG.iff_add_fg`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/GroupTheory/Finiteness.lean#L724-L725) — `mathlib-0933`

Snippet: `samples/mathlib/mathlib-0933.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: isAddFG_additive_iff
- **file**: Mathlib/GroupTheory/Finiteness.lean
- **derivation**: isAddFG_additive_iff.symm
- **proof_uses_it**: True
- **explanation**: `Group.FG G` is an abbrev for `IsMulFG G`, and `AddGroup.FG (Additive G)` is `IsAddFG (Additive G)`. `isAddFG_additive_iff : IsAddFG (Additive M) ↔ IsMulFG M` is the same statement with the sides swapped and the abbrevs unfolded, and it needs only `[Mul M]`. The theorem's own proof is `isAddFG_additive_iff.symm`. `Monoid.fg_iff_add_fg` is a second match: it has the same shape for monoids, and its proof is the same term. I did not search outside this file for a further duplicate.

### [`aemeasurable_id'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean#L461-L463) — `mathlib-0935`

Snippet: `samples/mathlib/mathlib-0935.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: aemeasurable_id
- **file**: Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean
- **derivation**: aemeasurable_id
- **explanation**: `aemeasurable_id : AEMeasurable id μ` (line 458, same file) has the same hypotheses and variables as the target. The target states `AEMeasurable (fun x => x) μ`. `id` unfolds to `fun x => x`, so the two statements are defeq and `exact aemeasurable_id` closes the goal. Both are proved by `measurable_id.aemeasurable`, so the target does not depend on any chain through itself. They differ only in how the identity function is written.

### [`IsPrimitiveRoot.card_nthRoots_one`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean#L664-L668) — `mathlib-0939`

Snippet: `samples/mathlib/mathlib-0939.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsPrimitiveRoot.card_nthRoots
- **file**: Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean
- **derivation**: by rw [h.card_nthRoots, if_pos ⟨ζ, h.pow_eq_one⟩]
- **proof_uses_it**: True
- **explanation**: `IsPrimitiveRoot.card_nthRoots` (line 636) says that for a primitive n-th root ζ and any a, `Multiset.card (nthRoots n a) = if ∃ α, α ^ n = a then n else 0`. Taking a = 1 gives the target. The condition `∃ α, α ^ n = 1` holds because ζ is a witness, so the `if` reduces to n. The current proof already does exactly this, using `ite_eq_left`. I found no other declaration stating this result. The other hits are `card_nthRoots`, which is only an upper bound (≤ n), and the downstream users `card_nthRootsFinset` and `Cyclotomic.Basic`, which depend on the target.

### [`Metric.IsCover.refl`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/MetricSpace/Cover.lean#L56-L56) — `mathlib-0947`

Snippet: `samples/mathlib/mathlib-0947.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SetRel.IsCover.refl
- **file**: Mathlib/Basic/Rel/Cover.lean
- **derivation**: SetRel.IsCover.refl {(x, y) | edist x y ≤ ε} s
- **proof_uses_it**: True
- **explanation**: Metric.IsCover ε s N is defined as SetRel.IsCover {(x, y) | edist x y ≤ ε} s N. SetRel.IsCover.refl (U : SetRel X X) [U.IsRefl] (s) : IsCover U s s is the general reflexivity statement. The metric version instantiates U with the edist ≤ ε entourage, whose IsRefl instance is declared a few lines earlier in the same file. The current proof applies it through SetRel.IsCover.rfl.

### [`Multiset.empty_or_exists_mem`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Multiset/ZeroCons.lean#L207-L208) — `mathlib-0949`

Snippet: `samples/mathlib/mathlib-0949.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Multiset.exists_mem_of_ne_zero
- **file**: Mathlib/Data/Multiset/ZeroCons.lean
- **derivation**: or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero
- **proof_uses_it**: True
- **explanation**: `Multiset.exists_mem_of_ne_zero : s ≠ 0 → ∃ a, a ∈ s` is a distinct declaration. The target is its disjunctive form `s = 0 ∨ ∃ a, a ∈ s`, which follows by `or_iff_not_imp_left` (the current proof). I found no other Mathlib lemma stating the disjunction directly. I searched Multiset/ZeroCons and grepped Mathlib for `empty_or_exists_mem`, `eq_zero_or_exists_mem` and `exists_mem_of_ne_zero`. The derivation is one line of pure logic glue, so I'm calling it a special case rather than a strict duplicate.

### [`isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean#L178-L182) — `mathlib-0955`

Snippet: `samples/mathlib/mathlib-0955.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
- **file**: Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean
- **derivation**: isMIntegralCurveAt_eventuallyEq_of_contMDiffAt BoundarylessManifold.isInteriorPoint hv hγ hγ' h
- **proof_uses_it**: True
- **explanation**: The general lemma `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt` (line 133) has the same conclusion and hypotheses, plus the extra hypothesis `I.IsInteriorPoint (γ t₀)`. The boundaryless statement is that lemma with the extra hypothesis supplied by `BoundarylessManifold.isInteriorPoint`. The current proof is exactly this one-line wrapper. The general lemma is a separate declaration and does not depend on the target. I found no other candidate: the only occurrences of this name in Mathlib are the general lemma, the target and one later use.

### [`List.reverse_cons'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/List/Basic.lean#L266-L267) — `mathlib-0957`

Snippet: `samples/mathlib/mathlib-0957.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: List.reverse_cons
- **file**: Init/Data/List/Basic.lean
- **derivation**: by rw [reverse_cons, concat_eq_append]
- **proof_uses_it**: True
- **explanation**: Lean core's `List.reverse_cons` states `reverse (a :: as) = reverse as ++ [a]`. The theorem is the same statement with `concat (reverse l) a` in place of `reverse l ++ [a]`. `List.concat_eq_append` (a core simp lemma, `as.concat a = as ++ [a]`) unfolds that, so `reverse_cons` plus this rewrite proves it. The current proof is exactly this. I found no core, Batteries or Mathlib lemma that states the `concat` form directly.

### [`MeasureTheory.Integrable.comp_mul_right'`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean#L208-L210) — `mathlib-0962`

Snippet: `samples/mathlib/mathlib-0962.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.integrable_comp_mul_right_iff
- **file**: Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean
- **derivation**: (integrable_comp_mul_right_iff g hR).2 hg
- **proof_uses_it**: True
- **explanation**: `integrable_comp_mul_right_iff (g : ℝ → F) {R} (hR : R ≠ 0) : (Integrable fun x => g (x * R)) ↔ Integrable g` is the iff form of the theorem. The theorem is its `.mpr` direction. The iff is a separate declaration, proved via `integrable_comp_smul_iff` (it uses neither the theorem nor `Integrable.comp_mul_right'`). I did not open its proof to check this, so the independence rests on the neighbouring `integrable_comp_mul_left_iff` using `integrable_comp_smul_iff`. `Integrable.comp_smul` for `E = ℝ` would also give the result, after `mul_comm`.

### [`Representation.asAlgebraHom_single`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RepresentationTheory/Basic.lean#L123-L126) — `mathlib-0963`

Snippet: `samples/mathlib/mathlib-0963.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidAlgebra.lift_single
- **file**: Mathlib/Algebra/MonoidAlgebra/Basic.lean
- **derivation**: MonoidAlgebra.lift_single ρ g r
- **proof_uses_it**: True
- **explanation**: `Representation.asAlgebraHom ρ` is defined as `MonoidAlgebra.lift k (Module.End k V) G ρ` (`asAlgebraHom_def` is `rfl`). The theorem is `MonoidAlgebra.lift_single` with A := Module.End k V and F := ρ. It states `lift R A M F (single a b) = b • F a`. The current proof is `simp only [asAlgebraHom_def, MonoidAlgebra.lift_single]`.

### [`Set.nonempty_of_ssubset`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Set/Basic.lean#L374-L375) — `mathlib-0971`

Snippet: `samples/mathlib/mathlib-0971.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.sdiff_nonempty
- **file**: Mathlib/Order/BooleanAlgebra/Set.lean
- **derivation**: Set.sdiff_nonempty.2 ht.2
- **explanation**: Set.sdiff_nonempty says (s \ t).Nonempty ↔ ¬ s ⊆ t. The theorem's goal (t \ s).Nonempty follows from ¬ t ⊆ s, which is ht.2 for ht : s ⊂ t. The current proof uses Set.nonempty_of_not_subset, which is the same kind of statement. That lemma is a distinct declaration with the same content, and it is the one the current proof applies.

### [`LinearMap.map_finsupp_linearCombination`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean#L454-L456) — `mathlib-0972`

Snippet: `samples/mathlib/mathlib-0972.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Finsupp.apply_linearCombination
- **file**: Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean
- **derivation**: Finsupp.apply_linearCombination R f g l
- **proof_uses_it**: True
- **explanation**: Finsupp.apply_linearCombination (line 95) states f (linearCombination R v l) = linearCombination R (f ∘ v) l for a linear map f : M →ₗ[R] M'. This is the same statement as the target, which is an alias that applies it directly. Its proof goes through linearCombination_linear_comp, so it does not depend on the target.

### [`CategoryTheory.Bicategory.whiskerLeft_hom_inv_whiskerRight`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Bicategory/Basic.lean#L215-L218) — `mathlib-0974`

Snippet: `samples/mathlib/mathlib-0974.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Bicategory.whiskerLeft_hom_inv
- **file**: Mathlib/CategoryTheory/Bicategory/Basic.lean
- **derivation**: exact whiskerLeft_hom_inv f (whiskerRightIso η k)
- **explanation**: The target says f ◁ (η.hom ▷ k) ≫ f ◁ (η.inv ▷ k) = 𝟙 (f ≫ g ≫ k). `whiskerLeft_hom_inv f ι` says f ◁ ι.hom ≫ f ◁ ι.inv = 𝟙 (f ≫ _) for any 2-isomorphism ι. Taking ι := whiskerRightIso η k, whose hom and inv are η.hom ▷ k and η.inv ▷ k, gives the target up to definitional unfolding of the structure projections. whiskerRightIso is defined later in the same file (line 242), so the current proof cannot use it, and the current proof is a direct `simp [← whiskerLeft_comp]`. I did not find a separate declaration that states this result exactly.

### [`supClosure_univ`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/SupClosed.lean#L260-L261) — `mathlib-0977`

Snippet: `samples/mathlib/mathlib-0977.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ClosureOperator.closure_top
- **file**: Mathlib/Order/Closure.lean
- **derivation**: by simpa using supClosure.closure_top
- **explanation**: `ClosureOperator.closure_top` says `c ⊤ = ⊤` for any closure operator on a partial order with a top element. `supClosure` is a `ClosureOperator (Set α)`, and `Set α` has `⊤ = Set.univ` (`Set.top_eq_univ`). Taking `c := supClosure` gives the statement, so the derivation is a single instantiation plus `simpa`. The current proof is `by simp`. That proof probably goes through `supClosure_eq_self` and `supClosed_univ`, or through `closure_top` itself. I did not check which. I found no other declaration with this exact statement; `supClosed_univ` and `supClosure_eq_self` are in the same file.

### [`CategoryTheory.Iso.inv_ext`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Iso.lean#L401-L403) — `mathlib-0987`

Snippet: `samples/mathlib/mathlib-0987.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Iso.hom_comp_eq_id
- **file**: Mathlib/CategoryTheory/Iso.lean
- **derivation**: ((Iso.hom_comp_eq_id f).1 hom_inv_id).symm
- **proof_uses_it**: True
- **explanation**: `Iso.hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X} : α.hom ≫ f = 𝟙 X ↔ f = α.inv` (line 208) contains `inv_ext` as its forward direction with the equation flipped. The current proof of `inv_ext` already does exactly this, so this is the same content with only `.mp` and `.symm` glue. A second candidate is `CategoryTheory.IsIso.inv_eq_of_hom_inv_id` (line 296), which would give `by simpa using IsIso.inv_eq_of_hom_inv_id hom_inv_id`. The `Iso.hom_comp_eq_id` proof is `rw [← eq_inv_comp, comp_id]`, so it does not depend on `inv_ext`.

### [`Minimal.le`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Order/Minimal.lean#L286-L288) — `mathlib-0992`

Snippet: `samples/mathlib/mathlib-0992.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MinimalFor.le
- **file**: Mathlib/Order/Minimal.lean
- **derivation**: exact MinimalFor.le (f := id) (minimalFor_id.mpr h) hy
- **explanation**: `MinimalFor.le (h : MinimalFor Q f i) (hj : Q j) : f i ≤ f j` is stated for a general `f : ι → α` into a linear order. `minimalFor_id : MinimalFor P id x ↔ Minimal P x` holds by `.rfl`, so `Minimal.le` is the case `f := id`, `ι := α`. The candidate's proof is independent of `Minimal.le`: it uses `MinimalFor.not_lt` and `le_of_not_gt`. The current proof of `Minimal.le` uses `Minimal.not_lt` instead. I found no other statement of `Minimal.le` elsewhere in Mathlib.

### [`Algebra.IsAlgebraic.tower_top`](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/Algebraic/Basic.lean#L472-L475) — `mathlib-0997`

Snippet: `samples/mathlib/mathlib-0997.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.IsAlgebraic.extendScalars
- **file**: Mathlib/RingTheory/Algebraic/Basic.lean
- **derivation**: Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective
- **proof_uses_it**: True
- **explanation**: Algebra.IsAlgebraic.extendScalars (line 442, same file) states that for commutative rings R, S with algebraMap R S injective and [Algebra.IsAlgebraic R A], Algebra.IsAlgebraic S A holds. The target is the case where R = K and S = L are fields. Their algebraMap is injective by `(algebraMap K L).injective`, which is a ring hom out of a field. The existing proof is exactly this one-line application. Nothing else in the file or in Integral.lean (the `isAlgebraic_iff` variants) states it more directly.


## Tau Ceti (35 flagged)

### [`TauCeti.IntegralLattice.evenSublattice_carrier_submoduleOf`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/IntegralLattice/Characteristic/EvenSublattice.lean#L86-L90) — `tauceti-0006`

Snippet: `samples/tauceti/tauceti-0006.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.comap_map_eq_of_injective
- **file**: Mathlib/Algebra/Module/Submodule/Map.lean
- **derivation**: rw [evenSublattice_carrier]; exact Submodule.comap_map_eq_of_injective L.carrier.injective_subtype _
- **proof_uses_it**: True
- **explanation**: `Submodule.submoduleOf N P` is by definition `N.comap P.subtype`. After rewriting with the library's `evenSublattice_carrier`, the carrier is `L.evenSubmodule.map L.carrier.subtype`. The goal is then `(p.map f).comap f = p` with `f = L.carrier.subtype`, injective. That is exactly `Submodule.comap_map_eq_of_injective`. The only other step is unfolding the definition of `submoduleOf`. The current proof already uses the Mathlib lemma. I found no Mathlib lemma that states the `submoduleOf` version directly.

### [`TauCeti.banachMazurDist_of_isEmpty`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Normed/Module/BanachMazur.lean#L91-L93) — `tauceti-0035`

Snippet: `samples/tauceti/tauceti-0035.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.iInf_of_isEmpty
- **file**: Mathlib/Data/Real/Archimedean.lean
- **derivation**: Real.iInf_of_isEmpty _
- **proof_uses_it**: True
- **explanation**: Mathlib has no Banach–Mazur distance. The theorem says that the infimum over an empty index type of real numbers is 0. `banachMazurDist` unfolds to `⨅ T : E ≃L[𝕜] F, ‖T‖ * ‖T.symm‖`. The statement is therefore `Real.iInf_of_isEmpty` applied to that function, with `IsEmpty (E ≃L[𝕜] F)` as the hypothesis. The current proof is already this one-line application. I did not open the Mathlib file to confirm the path or the exact statement of `Real.iInf_of_isEmpty`. The path above is from memory and may be wrong. If you prefer to count the content as lying in the library's own definition, `none_found` is the other defensible verdict.

### [`TauCeti.SheafOfModules.freePUnitIsoUnit_inv`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Category/ModuleCat/Sheaf/Free/Basic.lean#L78-L84) — `tauceti-0040`

Snippet: `samples/tauceti/tauceti-0040.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.coproductUniqueIso_inv
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Products.lean
- **derivation**: coproductUniqueIso_inv (fun _ : PUnit.{u + 1} ↦ _root_.SheafOfModules.unit.{v₁, u₁, u} S)
- **proof_uses_it**: True
- **explanation**: freePUnitIsoUnit is defined as coproductUniqueIso of the constant family S.unit over PUnit. Mathlib's coproductUniqueIso_inv (the to_dual of productUniqueIso_hom) says (coproductUniqueIso f).inv = Sigma.ι f default for Unique β. The target lemma is that statement with β = PUnit and f the constant family. SheafOfModules.ιFree is the coproduct inclusion. The library's own proof is this single application, so the lemma adds nothing beyond unfolding the definition. I did not open the definition of ιFree, so that identification is assumed.

### [`ContRepresentation.isUnitary_iff_norm_map`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Continuous/Unitary/Basic.lean#L51-L58) — `tauceti-0058`

Snippet: `samples/tauceti/tauceti-0058.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.norm_map_iff_inner_map_map
- **file**: Mathlib/Analysis/InnerProductSpace/LinearMap.lean
- **derivation**: forall_congr' fun g ↦ (LinearMap.norm_map_iff_inner_map_map (π g)).symm
- **proof_uses_it**: True
- **explanation**: IsUnitary π unfolds to ∀ g v w, ⟪π g v, π g w⟫ = ⟪v, w⟫. Mathlib's LinearMap.norm_map_iff_inner_map_map f says (∀ x, ‖f x‖ = ‖x‖) ↔ (∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) for a linear map class. Apply it to f = π g (a continuous linear map) and quantify over g. The existing proof does exactly this, split into the two directions. The remaining step is only routine quantifier glue, so the result is a short instantiation of the Mathlib lemma.

### [`TauCeti.tsum_inner_mul_inner_hermiteFunctionLp`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Parseval.lean#L50-L55) — `tauceti-0074`

Snippet: `samples/tauceti/tauceti-0074.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HilbertBasis.tsum_inner_mul_inner
- **file**: Mathlib/Analysis/InnerProductSpace/l2Space.lean
- **derivation**: simpa using (hermiteHilbertBasis 𝕜).tsum_inner_mul_inner f g
- **proof_uses_it**: True
- **explanation**: Mathlib's HilbertBasis.tsum_inner_mul_inner states ∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ for any Hilbert basis b. The theorem is this statement with b the library's Hermite Hilbert basis on L²(ℝ), where b n is simp-rewritten to hermiteFunctionLp 𝕜 n. The proof is a single application of Mathlib's lemma. The Hermite-specific content (that the Hermite functions form a Hilbert basis) lives in the library's definition hermiteHilbertBasis, not in this theorem.

### [`TauCeti.PathAlgebra.quadraticDualMk_apply`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/Quiver/PathAlgebra/Quadratic/Dual.lean#L222-L225) — `tauceti-0090`

Snippet: `samples/tauceti/tauceti-0090.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.mkₐ_eq_mk
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: by rw [quadraticDualMk, Ideal.Quotient.mkₐ_eq_mk]
- **proof_uses_it**: True
- **explanation**: quadraticDualMk is defined as Ideal.Quotient.mkₐ k _ for the quadratic dual ideal. The theorem says its coercion to a function equals Ideal.Quotient.mk. That is Mathlib's Ideal.Quotient.mkₐ_eq_mk (⇑(mkₐ R I) = mk I), instantiated at the ring (pathAlgebra k Q)ᵐᵒᵖ and the ideal (quadraticDualIdeal k Q R).asIdeal. The only extra step is unfolding the definition, and the proof is a single rw. The result is a special case rather than a duplicate because Mathlib's declaration is stated for a specific ideal and ring, and the library's own definition needs unfolding first.

### [`AlgebraicGeometry.Scheme.Hom.normalizationMap_fromNormalization`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/Normalization/Basic.lean#L60-L64) — `tauceti-0110`

Snippet: `samples/tauceti/tauceti-0110.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp
- **file**: Mathlib/AlgebraicGeometry/Normalization.lean
- **derivation**: by unfold normalizationMap; exact f.normalizationDesc_comp _ _ _
- **proof_uses_it**: True
- **explanation**: Mathlib's `normalizationDesc_comp` (@[reassoc, simp]) says `f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization`. `normalizationMap` is defined as `f.normalizationDesc (φ ≫ g.toNormalization) g.fromNormalization _`, so the theorem is this lemma with f₁ := φ ≫ g.toNormalization and f₂ := g.fromNormalization, after unfolding the definition. The current proof `simp [normalizationMap]` already uses the lemma as a simp lemma. I could not run Lean, so the derivation is not compiled.

### [`CategoryTheory.Sheaf.H.exact_δ_map`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/CategoryTheory/Sites/SheafCohomology/LongExactSequence.lean#L84-L88) — `tauceti-0219`

Snippet: `samples/tauceti/tauceti-0219.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Sheaf.H.longSequence_exact₁'
- **file**: Mathlib/CategoryTheory/Sites/SheafCohomology/ExactSequences.lean
- **derivation**: (ShortComplex.ab_exact_iff_function_exact _).mp (longSequence_exact₁' hS n₀ n₁ h)
- **proof_uses_it**: True
- **explanation**: Mathlib's `longSequence_exact₁'` states that the short complex `ofHom (δ hS n₀ n₁ h) → ofHom (map S.f n₁)` in `AddCommGrpCat` is `ShortComplex.Exact`. The target is the same exactness statement phrased as `Function.Exact` on the underlying maps. The two are related by `ShortComplex.ab_exact_iff_function_exact`, which is exactly what the current proof does. I found no Mathlib declaration that states this directly in `Function.Exact` form.

### [`TauCeti.DenseGraphLimits.SymmKernel.rectIntegral_eq_setIntegral_setIntegral`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Combinatorics/DenseGraphLimits/Kernel/Integral.lean#L77-L82) — `tauceti-0291`

Snippet: `samples/tauceti/tauceti-0291.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.setIntegral_prod
- **file**: Mathlib/MeasureTheory/Integral/Prod.lean
- **derivation**: rw [rectIntegral_def]
exact setIntegral_prod _ K.integrable_uncurry.integrableOn
- **proof_uses_it**: True
- **explanation**: `rectIntegral μ S T` is defined as `∫ p in S ×ˢ T, K p.1 p.2 ∂(μ.prod μ)`. Mathlib's `setIntegral_prod` states `∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ` for `f` integrable on `s ×ˢ t`. The theorem is this lemma with `f := fun p => K p.1 p.2` and `ν := μ`. The integrability hypothesis comes from the library's own `K.integrable_uncurry`. The current proof already does exactly this: it unfolds the definition and applies `setIntegral_prod`. I found no declaration that states the result directly for `SymmKernel`, since that type is specific to this library.

### [`TauCeti.CoveringSpace.proj_hom_comp_hom_left_hom`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Covering/Category.lean#L182-L186) — `tauceti-0299`

Snippet: `samples/tauceti/tauceti-0299.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Over.w
- **file**: Mathlib/CategoryTheory/Comma/Over/Basic.lean
- **derivation**: by rw [← TopCat.coe_comp, CategoryTheory.Over.w]
- **proof_uses_it**: True
- **explanation**: The statement is the commuting triangle of a morphism in the full subcategory of `TopCat / X`, written as an equality of underlying functions. A morphism `f : p ⟶ q` of covering spaces is a morphism `f.hom` in `Over X`, so Mathlib's `Over.w` gives `f.hom.left ≫ q.obj.hom = p.obj.hom`. The only extra step is `TopCat.coe_comp`, which turns the composite into function composition. The library's `w` is itself `Over.w _`, and the current proof applies it. I did not re-check `Over.w`'s exact statement or `TopCat.coe_comp` in the Mathlib sources. Mathlib has no `CoveringSpace` category, and I found no function-level version of this lemma for `Over`.

### [`Ideal.rightTensorIdeal_iSup`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/TensorProduct/Ideal.lean#L154-L159) — `tauceti-0325`

Snippet: `samples/tauceti/tauceti-0325.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.map_iSup
- **file**: Mathlib/RingTheory/Ideal/Maps.lean
- **derivation**: Ideal.map_iSup (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom I
- **proof_uses_it**: True
- **explanation**: `rightTensorIdeal R A I` is defined as `Ideal.map includeRight.toRingHom I`, so the statement is `Ideal.map_iSup` for `f := includeRight.toRingHom` after unfolding that definition. The library's own proof is exactly that one application. Mathlib has no `rightTensorIdeal` of its own, so the match is only through the unfolded definition. I grepped Mathlib for `rightTensorIdeal` and found nothing, and I read the statement of `Ideal.map_iSup` at line 243 of `Maps.lean`.

### [`TauCeti.PresentedK0.map_mk`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/CategoryTheory/GrothendieckGroup/Presentation.lean#L394-L397) — `tauceti-0327`

Snippet: `samples/tauceti/tauceti-0327.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuotientAddGroup.map_mk
- **file**: Mathlib/GroupTheory/QuotientGroup/Defs.lean
- **derivation**: QuotientAddGroup.map_mk _ _ _ _ _
- **proof_uses_it**: True
- **explanation**: PresentedK0.map is defined as QuotientAddGroup.map (closure relsC) (closure relsD) (freeMap F) _, and mk as QuotientAddGroup.mk' (closure rels). The Mathlib lemma `QuotientAddGroup.map_mk` says `map N M f h ↑x = ↑(f x)`, which is this statement after unfolding the definitions and setting N = closure relsC, M = closure relsD, f = freeMap F. The current proof is exactly that lemma. The only content is the unfolding of the library's own wrappers around Mathlib's quotient map. The lemma is therefore a specialization of Mathlib's.

### [`TauCeti.ClassFunction.characterPairing_ofFDRep_self`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/CharacterTable/Pairing.lean#L257-L264) — `tauceti-0332`

Snippet: `samples/tauceti/tauceti-0332.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FDRep.char_orthonormal
- **file**: Mathlib/RepresentationTheory/Character.lean
- **derivation**: rw [characterPairing_ofFDRep]; simpa [Nonempty.intro (CategoryTheory.Iso.refl V)] using FDRep.char_orthonormal V V
- **proof_uses_it**: True
- **explanation**: Mathlib's `FDRep.char_orthonormal V W` (for simple V, W over an algebraically closed field with invertible |G|) gives (|G|)⁻¹ * ∑ g, V.character g * W.character g⁻¹ = if Nonempty (V ≅ W) then 1 else 0. The target is its V = W case, stated with the library's `characterPairing`/`ofFDRep`, which unfold to that sum. The `if` reduces to 1 because `Iso.refl V` shows `Nonempty (V ≅ V)`. Mathlib does the same instantiation at `FinGroupCharZero.lean:125`. The library's proof reaches `char_orthonormal` through `characterPairing_ofFDRep_orthonormal`. The only glue is the library's own unfolding lemma `characterPairing_ofFDRep`, so this is borderline.

### [`TauCeti.ClassData.sum_card_classFinset`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/CharacterTable/Dixon/ClassData/Basic.lean#L366-L371) — `tauceti-0354`

Snippet: `samples/tauceti/tauceti-0354.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.card_eq_sum_card_fiberwise
- **file**: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
- **derivation**: by simpa [classFinset, Finset.card_univ] using (Finset.card_eq_sum_card_fiberwise (f := d.index) (s := Finset.univ) (t := Finset.univ) fun _ _ => Finset.mem_univ _).symm
- **proof_uses_it**: True
- **explanation**: `classFinset i` is `{g | d.index g = i}`, the fiber of `d.index : G → Fin d.numClasses` over `i` (a filter of `univ`). The theorem is `Finset.card_eq_sum_card_fiberwise` (`#s = ∑ b ∈ t, #{a ∈ s | f a = b}` given `MapsTo f s t`) with `s = t = univ` and `f = d.index`, plus `Finset.card_univ`. The library's proof already does this. I found no Mathlib lemma that states it directly for `Fintype`. The derivation has not been compiled, and the `simpa` call may need adjusting.

### [`TauCeti.SSet.S1.hom_ext`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/SimplicialSet/Pointed/Circle.lean#L85-L88) — `tauceti-0410`

Snippet: `samples/tauceti/tauceti-0410.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.coequalizer.hom_ext
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Equalizers.lean
- **derivation**: coequalizer.hom_ext h
- **proof_uses_it**: True
- **explanation**: Mathlib has no `hom_ext` specific to `SSet.S1`. It defines `SSet.S1` as the colimit of `parallelPair (δ 0) (δ 1)`, which is the coequalizer of the two vertex inclusions. The library's `quotient` is `coequalizer.π (δ 0) (δ 1)`. The target lemma is therefore `coequalizer.hom_ext` with f := δ 0 and g := δ 1, after unfolding `S1` and `quotient`. The current proof is exactly `coequalizer.hom_ext h`. I did not open the source of `coequalizer.hom_ext` to confirm its file path and statement. The path above is from memory.

### [`TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem.principalHom_injective_of_principalKernel_eq_bot`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicGeometry/WeilDivisor/Principal/Kernel.lean#L82-L86) — `tauceti-0418`

Snippet: `samples/tauceti/tauceti-0418.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddMonoidHom.ker_eq_bot_iff
- **file**: Mathlib/Algebra/Group/Subgroup/Ker.lean
- **derivation**: (AddMonoidHom.ker_eq_bot_iff S.principalHom).mp h
- **proof_uses_it**: True
- **explanation**: principalKernel is an abbrev for S.principalHom.ker, so the statement is `f.ker = ⊥ → Function.Injective f` for f := S.principalHom. This is the forward direction of Mathlib's `AddMonoidHom.ker_eq_bot_iff`. The library's proof goes through the local `principalKernel_eq_bot_iff`, which itself is exactly that Mathlib lemma.

### [`TauCeti.Iwasawa.algebraMap_mem_pseudomeasures`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RingTheory/Iwasawa/Pseudomeasure.lean#L90-L92) — `tauceti-0428`

Snippet: `samples/tauceti/tauceti-0428.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.one_le_one_div
- **file**: Mathlib/Algebra/Algebra/Operations.lean
- **derivation**: (Submodule.one_le_one_div.2 (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact Submodule.algebraMap_mem _))) (Submodule.algebraMap_mem r)
- **explanation**: `pseudomeasures δ Q` is defined as `1 / span R (range fun g => algebraMap R Q (δ g - 1))`. Mathlib's `Submodule.one_le_one_div : 1 ≤ 1 / I ↔ I ≤ 1` gives `1 ≤ pseudomeasures δ Q` once the span is shown to be `≤ 1`. The span is `≤ 1` by `span_le`, because each generator is `algebraMap _ _ _` and so lies in `1` by `Submodule.algebraMap_mem`. Then `algebraMap R Q r ∈ 1` is `Submodule.algebraMap_mem r`. This is a one-line instantiation of the Mathlib lemma. The side goal is a small `span_le` step, so it is borderline against the two-line limit. The library's own proof goes through `mem_pseudomeasures_iff` and does not use this lemma.

### [`TauCeti.ker_leftNumericalQuotientMk`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/SesquilinearForm/NumericalQuotient/Basic.lean#L161-L164) — `tauceti-0448`

Snippet: `samples/tauceti/tauceti-0448.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.ker_mkQ
- **file**: Mathlib/LinearAlgebra/Quotient/Basic.lean
- **derivation**: (leftRadical b).ker_mkQ
- **proof_uses_it**: True
- **explanation**: I did not open Mathlib to read `Submodule.ker_mkQ`'s statement or check its file path. The file path above is from memory and unchecked, and the statement is also from memory: `ker p.mkQ = p` for a submodule `p`. `leftNumericalQuotientMk b` is defined in the library as `(leftRadical b).mkQ`. So the theorem is `Submodule.ker_mkQ` applied to `p := leftRadical b`, after unfolding that definition. The library's own proof is exactly this one application. I only searched the library's own file, where the definition and proof sit.

### [`TauCeti.continuous_restrictedProductCongrRight`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Algebra/RestrictedProduct/Congr/Right.lean#L120-L133) — `tauceti-0468`

Snippet: `samples/tauceti/tauceti-0468.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: RestrictedProduct.mapAlong_continuous
- **file**: Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean
- **derivation**: exact RestrictedProduct.mapAlong_continuous _ _ id Filter.tendsto_id (fun i ↦ φ i) (hφ.mono fun _ h ↦ h.mapsTo) hcont
- **explanation**: `restrictedProductCongrRight U U' φ hφ` is, as a function, `fun x => ⟨fun i => φ i (x i), _⟩`, which is definitionally `RestrictedProduct.mapAlong G H id tendsto_id (fun i => φ i) _`. Mathlib's `mapAlong_continuous` says `mapAlong` is continuous when each `φ j` is. Taking `f = id`, `A₁ i = (U i : Set _)` and `A₂ i = (U' i : Set _)` gives the theorem. The `MapsTo` hypothesis comes from `Set.BijOn.mapsTo`. I did not check that `exact` accepts the definitional unfolding of the coercion. If it doesn't, the existing `convert ... using 1; ext x i; simp` pattern would close the goal instead. The library's current proof does not use this declaration. It uses the library's own `continuous_restrictedProductMap`, which is the same kind of statement.

### [`selfAdjoint.isHermitian_coe`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Measure/SymmetricMatrix/Basic.lean#L201-L205) — `tauceti-0505`

Snippet: `samples/tauceti/tauceti-0505.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.IsSelfAdjoint.isHermitian
- **file**: Mathlib/LinearAlgebra/Matrix/Hermitian.lean
- **derivation**: IsSelfAdjoint.isHermitian A.2
- **explanation**: The theorem says that a matrix lying in `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)` is Hermitian. Membership in that submodule unfolds to `IsSelfAdjoint`. The Mathlib alias `IsSelfAdjoint.isHermitian` (declared as `protected alias ⟨_, _root_.IsSelfAdjoint.isHermitian⟩` in the Matrix namespace, so the full name is `IsSelfAdjoint.isHermitian`) turns `IsSelfAdjoint A` into `A.IsHermitian`. Applying it to `A.2` gives the result. The current proof uses `A.2` directly and relies on definitional unfolding.

### [`TauCeti.heightLinearMap_apply`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/RootSystem/Height.lean#L70-L73) — `tauceti-0524`

Snippet: `samples/tauceti/tauceti-0524.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Module.Basis.coe_sumCoords
- **file**: Mathlib/LinearAlgebra/Basis/Defs.lean
- **derivation**: congrFun (Module.Basis.coe_sumCoords b.toWeightBasis) m
- **proof_uses_it**: True
- **explanation**: heightLinearMap P b is defined as b.toWeightBasis.sumCoords. Mathlib's `Module.Basis.coe_sumCoords` states `(b.sumCoords : M → R) = fun m => (b.repr m).sum fun _ => id`. The target is this statement applied at m, with the basis instantiated to b.toWeightBasis and heightLinearMap unfolded. The current proof already uses it via `rw`.

### [`TauCeti.singularChainFiltrationIso_hom_comp_singularChainFiltrationι`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/Singular/FilteredSpace.lean#L112-L118) — `tauceti-0528`

Snippet: `samples/tauceti/tauceti-0528.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk
- **file**: Mathlib/CategoryTheory/Subobject/Basic.lean
- **derivation**: Subobject.underlyingIso_hom_comp_eq_mk _
- **proof_uses_it**: True
- **explanation**: Mathlib's lemma states `(underlyingIso f).hom ≫ f = (mk f).arrow` for a mono `f`. Instantiating `f := singularChainFiltrationι R X q` gives the target. By definition, `singularChainFiltrationIso` is `underlyingIso` of that map and `singularChainFiltration` is `Subobject.mk` of it. The library's proof is exactly this application. The mono instance is supplied by the library's own instance, which is an argument instantiation.

### [`TauCeti.Green.Division.integrableOn_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Green/Division/Basic.lean#L55-L59) — `tauceti-0577`

Snippet: `samples/tauceti/tauceti-0577.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.integrableOn_finset_iUnion
- **file**: Mathlib/MeasureTheory/Integral/IntegrableOn.lean
- **derivation**: by rw [← V.covers]; exact integrableOn_finset_iUnion
- **proof_uses_it**: True
- **explanation**: The theorem is `integrableOn_finset_iUnion` instantiated with the finset `V.cells` and the family `fun K => K.region d`. The only extra step is rewriting D as the union of the cells by `V.covers`. The existing proof already does this.

### [`TopologicalAbelianization.map_mk`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Topology/Algebra/Group/TopologicalAbelianization.lean#L120-L124) — `tauceti-0623`

Snippet: `samples/tauceti/tauceti-0623.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuotientGroup.map_mk
- **file**: Mathlib/GroupTheory/QuotientGroup/Basic.lean
- **derivation**: QuotientGroup.map_mk _ _ _ _ x
- **proof_uses_it**: True
- **explanation**: Mathlib has no TopologicalAbelianization.map (its TopologicalAbelianization file contains no `map`). The library defines `TopologicalAbelianization.map f hf` as `QuotientGroup.map _ _ f (topologicalClosure_commutator_le_comap f hf)`. So `map_mk` is `QuotientGroup.map_mk` (the map sends the class of x to the class of f x) with the closed commutator subgroups plugged in, after unfolding `map`. I did not open QuotientGroup.map_mk in Mathlib to confirm its exact statement and file path, so the file path is from memory. The library's proof is already exactly this term. A reviewer could instead say the content lies in the library's own definition of `map`. I judged it a special case because the content is the generic quotient-map lemma.

### [`TauCeti.Subcomodule.coact_mem_tensor_top`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Coalgebra/Subcomodule/Basic.lean#L177-L185) — `tauceti-0647`

Snippet: `samples/tauceti/tauceti-0647.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TensorProduct.map_surjective
- **file**: Mathlib/LinearAlgebra/TensorProduct/RightExactness.lean
- **derivation**: LinearMap.mem_range.mpr (TensorProduct.map_surjective (fun m ↦ ⟨⟨m, Submodule.mem_top⟩, rfl⟩) Function.surjective_id _)
- **proof_uses_it**: True
- **explanation**: The goal says that an element of M ⊗ C, here `coact m`, lies in the range of `map (⊤ : Submodule R M).subtype id`. That range is everything because `⊤.subtype` and `id` are both surjective. `TensorProduct.map_surjective` says exactly that the tensor map of two surjective linear maps is surjective. Applying it to `⊤.subtype` and `LinearMap.id`, then `LinearMap.mem_range`, gives the goal for any element, not only `coact m`. The only glue is the one-line surjectivity of `⊤.subtype`. Mathlib has no `Subcomodule` declarations, and I found no more direct lemma about the range of `map ⊤.subtype id`, so the library's current proof is already this derivation.

### [`TauCeti.quotientStabilizerEquiv_mk`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/GroupTheory/GroupAction/Transitive.lean#L93-L98) — `tauceti-0654`

Snippet: `samples/tauceti/tauceti-0654.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MulAction.ofQuotientStabilizer_mk
- **file**: Mathlib/GroupTheory/GroupAction/Quotient.lean
- **derivation**: ofQuotientStabilizer_mk G b g
- **proof_uses_it**: True
- **explanation**: Mathlib has no equivalence `G ⧸ stabilizer G b ≃ X` for transitive actions, so `quotientStabilizerEquiv` is the library's own definition. It is `Equiv.ofBijective (ofQuotientStabilizer G b) _`, so its coercion unfolds definitionally to Mathlib's `MulAction.ofQuotientStabilizer`. Mathlib's `ofQuotientStabilizer_mk` (line 146) states `ofQuotientStabilizer G x (QuotientGroup.mk g) = g • x`, which is this statement once the definition is unfolded. The current proof is exactly that term. I searched Mathlib for other equivalences between the coset space and `X` and found only `orbitEquivQuotientStabilizer`, which goes through the orbit, not `X`. This is a borderline call, since the match depends on unfolding the library's definition.

### [`TauCeti.Probability.coinKernel_apply_true`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Probability/Exchangeability/ConditionallyIID/CoinFlips.lean#L77-L81) — `tauceti-0724`

Snippet: `samples/tauceti/tauceti-0724.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem
- **file**: Mathlib/Probability/Distributions/Bernoulli.lean
- **derivation**: rw [coinKernel_toMeasure]
exact bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) rfl (by simp)
- **proof_uses_it**: True
- **explanation**: Mathlib's `bernoulliMeasure_apply_of_mem_of_notMem` says Ber(x, y, p) s = toNNReal p when s is measurable, x ∈ s and y ∉ s. The theorem is the case X = Bool, x = true, y = false, s = {true}, after unfolding `coinKernel` to `bernoulliMeasure true false p` (`rfl`). The only extra work is the side goal `false ∉ {true}`, closed by `simp`. The current proof already does exactly this.

### [`AddSubgroup.natDegree_additivePolynomial`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Polynomial/AdditivePolynomial.lean#L80-L83) — `tauceti-0768`

Snippet: `samples/tauceti/tauceti-0768.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Lagrange.natDegree_nodal
- **file**: Mathlib/LinearAlgebra/Lagrange.lean
- **derivation**: by rw [additivePolynomial, Lagrange.natDegree_nodal, Finset.card_univ]
- **proof_uses_it**: True
- **explanation**: `additivePolynomial` is defined as `Lagrange.nodal Finset.univ (↑)` (a library-local definition, not in Mathlib). Mathlib's `Lagrange.natDegree_nodal` gives `(nodal s v).natDegree = #s` for nontrivial R. Instantiating s = univ, v = coe and using `Finset.card_univ` gives the statement. The proof is exactly this, so the result is a special case, but it is essentially the definition unfolded.

### [`PiLp.dist_le_sqrt_card_mul_dist_ofLp`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Normed/Lp/PiLp.lean#L132-L137) — `tauceti-0777`

Snippet: `samples/tauceti/tauceti-0777.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PiLp.antilipschitzWith_ofLp
- **file**: Mathlib/Analysis/Normed/Lp/PiLp.lean
- **derivation**: simpa [NNReal.coe_rpow, Real.sqrt_eq_rpow] using (PiLp.antilipschitzWith_ofLp 2 β).le_mul_dist x y
- **explanation**: Mathlib has `PiLp.antilipschitzWith_ofLp : AntilipschitzWith ((card ι : ℝ≥0) ^ (1 / p).toReal) ofLp`. `AntilipschitzWith.le_mul_dist` turns it into `dist x y ≤ K * dist (ofLp x) (ofLp y)`. Taking p = 2 gives K = card ^ (1/2) = √card, which is what the theorem states. The existing proof does the same with `lipschitzWith_toLp` and the same simp glue, so it is a one-line instantiation. I found no Mathlib lemma that states the √card form directly. I grepped for `sqrt card`, `√(Fintype.card` and `dist_le_*ofLp` and found nothing that matches. I did not run the derivation, so the simp step is unchecked.

### [`TauCeti.Contour.windingNumber_circle`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Contour/Winding/Number/Circle.lean#L121-L131) — `tauceti-0792`

Snippet: `samples/tauceti/tauceti-0792.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: circleIntegral.integral_sub_center_inv
- **file**: Mathlib/MeasureTheory/Integral/CircleIntegral.lean
- **derivation**: have h := circleIntegral.integral_sub_center_inv c hr
simp only [circleIntegral, smul_eq_mul, ← div_eq_mul_inv] at h; rw [h]; exact inv_mul_cancel₀ (by simp [Real.pi_ne_zero])
- **explanation**: Mathlib's `circleIntegral.integral_sub_center_inv (c : ℂ) {R : ℝ} (hR : R ≠ 0) : (∮ z in C(c, R), (z - c)⁻¹) = 2 * π * I` has the same hypothesis r ≠ 0. Unfolding `circleIntegral` gives `∫ θ in 0..2π, deriv (circleMap c R) θ • (circleMap c R θ - c)⁻¹`. This is the theorem's integral, once `•` becomes `*` and `x * y⁻¹` becomes `x / y`. The theorem is then `(2πI)⁻¹ * (2πI) = 1`. The library's own docstring notes that the value follows from this lemma. The derivation is about two to three short lines and the exact simp normal form is untested, so this is a borderline `special_case`.

### [`TauCeti.asAlgebraHom_blockRepresentation`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/RepresentationTheory/CharacterTable/BlockRepresentation.lean#L96-L104) — `tauceti-0825`

Snippet: `samples/tauceti/tauceti-0825.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidAlgebra.lift_unique'
- **file**: Mathlib/Algebra/MonoidAlgebra/Basic.lean
- **derivation**: (MonoidAlgebra.lift_unique' (blockAlgHom e i)).symm
- **explanation**: Mathlib's `MonoidAlgebra.lift_unique'` says any algebra hom `F : R[M] →ₐ[R] A` equals `lift R A M ((F : R[M] →* A).comp (of R M))`. `Representation.asAlgebraHom ρ` is defined as `lift k _ G ρ`, and `blockRepresentation e i` is defined as `(blockAlgHom e i).toMonoidHom.comp (MonoidAlgebra.of k G)`. So taking `F := blockAlgHom e i` gives the theorem, with `.symm` and definitional unfolding of `asAlgebraHom` and `blockRepresentation`. I could not run Lean, so I did not check that the `toMonoidHom` and coercion forms unify. If they don't, `by rw [Representation.asAlgebraHom_def]; exact (MonoidAlgebra.lift_unique' _).symm` should work.

### [`IntermediateField.extendRight_le_iff`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/FieldTheory/IntermediateField/ExtendRight.lean#L44-L54) — `tauceti-0837`

Snippet: `samples/tauceti/tauceti-0837.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IntermediateField.map_le_iff_le_comap
- **file**: Mathlib/FieldTheory/IntermediateField/Basic.lean
- **derivation**: rw [extendRight_eq_map, map_le_iff_le_comap]
exact Iff.rfl
- **explanation**: `extendRight F M` is `F.map (Algebra.algHom K L M)`, which is `rfl`-equal to `F.map (IsScalarTower.toAlgHom K L M)`. Mathlib's `map_le_iff_le_comap` states `s.map f ≤ t ↔ s ≤ t.comap f`. Take f to be the algebra map L → M. Then `F ≤ E.comap f` unfolds definitionally to `∀ x ∈ F, algebraMap L M x ∈ E`, so the target follows by unfolding. I could not run Lean, so the final `Iff.rfl` step is unchecked. It relies on that definitional unfolding going through. Mathlib's own `ExtendRight.lean` has no order or membership lemma for `extendRight`, so there is no direct duplicate.

### [`TauCeti.Deck.normalizerQuotient_one_smul_subgroupFiberOrbitClass`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/AlgebraicTopology/UniversalCover/Deck/NormalizerQuotient/FiberAction.lean#L164-L168) — `tauceti-0881`

Snippet: `samples/tauceti/tauceti-0881.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: one_smul
- **file**: Mathlib/Algebra/Group/Action/Defs.lean
- **derivation**: exact one_smul _ _
- **proof_uses_it**: True
- **explanation**: The statement is `1 • x = x` for the `MulAction` of `Subgroup.normalizerQuotient H` on `SubgroupFiberOrbitQuotient H b`. That action is declared as an instance in the same file. Mathlib's `one_smul (b : α) : (1 : M) • b = b` covers it with M and α set to those types. The current `simp` proof closes the goal with `one_smul`, which is a simp lemma.

### [`TauCeti.IsDGRightModule.iSup_cyclesDeg_eq_top`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Homology/DG/Module/Right/Cohomology.lean#L234-L237) — `tauceti-0953`

Snippet: `samples/tauceti/tauceti-0953.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: DirectSum.IsInternal.submodule_iSup_eq_top
- **file**: Mathlib/Algebra/DirectSum/Module.lean
- **derivation**: (DirectSum.Decomposition.isInternal hM.cyclesDeg).submodule_iSup_eq_top
- **proof_uses_it**: True
- **explanation**: Mathlib's `DirectSum.IsInternal.submodule_iSup_eq_top` says that an internal direct sum of submodules has `iSup A = ⊤`. `DirectSum.Decomposition.isInternal` in `Mathlib/Algebra/DirectSum/Decomposition.lean` turns any `Decomposition` into `IsInternal`. The theorem instantiates these two lemmas at the family `hM.cyclesDeg`. The library supplies the `Decomposition hM.cyclesDeg` instance (lines 228–229). The proof is the one-line application of the two lemmas, so I count it as a special case. I did not find a single Mathlib lemma that states `Decomposition ℳ → ⨆ i, ℳ i = ⊤` directly.

### [`TauCeti.measurePreserving_conj`](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/MeasureTheory/Group/Conjugation.lean#L98-L103) — `tauceti-0999`

Snippet: `samples/tauceti/tauceti-0999.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.measurePreserving_smul
- **file**: Mathlib/MeasureTheory/Group/Action.lean
- **derivation**: measurePreserving_smul (ConjAct.toConjAct h) μ
- **proof_uses_it**: True
- **explanation**: Mathlib's `measurePreserving_smul (c : M) (μ) [SMulInvariantMeasure M α μ] : MeasurePreserving (c • ·) μ μ` is instantiated with M := ConjAct G, α := G and c := toConjAct h. Then `c • g` is definitionally `h * g * h⁻¹`. This is also exactly the library's one-line proof. I found no conjugation-specific lemma in Mathlib/MeasureTheory (no `ConjAct` there), so this is the closest match.


## Lean Pool (58 flagged)

### [`TauCeti.DavisKahanExt.starProjection_map_reflection`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/InfiniteDimensional/DoubleAngleSpectrum.lean#L475-L484) — `lean-pool-0007`

Snippet: `samples/lean-pool/lean-pool-0007.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.starProjection_map_apply
- **file**: Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean
- **derivation**: ext x
exact Submodule.starProjection_map_apply V.reflection U x
- **proof_uses_it**: True
- **explanation**: Mathlib's `starProjection_map_apply` says that for a linear isometry equivalence f, `(p.map f).starProjection x = f (p.starProjection (f.symm x))`. The theorem instantiates f with `V.reflection` and packages the right-hand side as the library's own definition `conjByIsometryEquiv W A = W ∘L A ∘L W.symm`. After `ext x`, the goal is this lemma up to unfolding that definition, which `rfl` handles. The current proof does exactly this. I found no operator-level version in Mathlib; the only match for `starProjection_map` was the pointwise lemma.

### [`AVenhance.Infra.Parabolic.FourierGalerkin.Modes.mFourier_star_at`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/RealModes/Modes.lean#L139-L142) — `lean-pool-0010`

Snippet: `samples/lean-pool/lean-pool-0010.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: UnitAddTorus.mFourier_neg
- **file**: Mathlib/Analysis/Fourier/AddCircleMulti.lean
- **derivation**: by rw [Complex.star_def]; exact (UnitAddTorus.mFourier_neg (n := k) (x := x)).symm
- **proof_uses_it**: True
- **explanation**: Mathlib's `UnitAddTorus.mFourier_neg` states `mFourier (-n) x = conj (mFourier n x)`. The theorem's `star z` on ℂ is `conj z` by `Complex.star_def`, which is definitional. So the theorem is `mFourier_neg` with the equation flipped and `star` written for `conj`. The current proof already applies it. I assumed `Torus` unfolds to `UnitAddTorus (Fin 2)`, since the existing proof type-checks against `mFourier_neg`.

### [`CIV.abs_min_sub_min_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CIVAxisymmetric/Zoom/DriftExtraction.lean#L349-L354) — `lean-pool-0012`

Snippet: `samples/lean-pool/lean-pool-0012.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: abs_min_sub_min_le_max
- **file**: Mathlib/Algebra/Order/Group/MinMax.lean
- **derivation**: by simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))] using abs_min_sub_min_le_max a c b c
- **explanation**: Mathlib has `abs_min_sub_min_le_max (a b c d) : |min a b - min c d| ≤ max |a - c| |b - d|`. Taking (a, c, b, c) gives max |a-b| |c-c|, which simplifies to |a-b|. This is the same one-line `simpa` that Mathlib uses for the max version, `abs_max_sub_max_le_abs`. Mathlib has no `abs_min_sub_min_le_abs` for min with a shared argument, so this is a special case rather than an exact duplicate. The library's own proof goes through `lipschitzWith_min` instead.

### [`LeanPolyABC.prime_dvd_radical_iff`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanPolyABC/Lib/Radical.lean#L120-L128) — `lean-pool-0027`

Snippet: `samples/lean-pool/lean-pool-0027.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible
- **file**: Mathlib/RingTheory/Radical/Basic.lean
- **derivation**: exact UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible hp.irreducible ha
- **explanation**: Mathlib's `dvd_radical_iff_of_irreducible (ha : Irreducible a) (hb : b ≠ 0) : a ∣ radical b ↔ a ∣ b` is the same statement. Mathlib's `radical` is `(primeFactors a).prod id`, with `primeFactors a = (normalizedFactors a).toFinset`. The library defines its own `LeanPolyABC.radical` and `primeFactors` with identical bodies. Because those definitions are the same, the library's `radical` should unfold to Mathlib's, possibly after `simpa [radical, primeFactors]` to line up the classical `DecidableEq` instances. The library hypothesis `Prime p` gives `Irreducible p` via `hp.irreducible`. I did not check whether Mathlib's `UniqueFactorizationMonoid` section needs different typeclass assumptions on `α` than the library's `CommMonoidWithZero` plus `NormalizationMonoid`. Mathlib's own proof uses the same ingredients as the library's: `radical_dvd_self` and `exists_mem_normalizedFactors_of_dvd`.

### [`CIV.polarR_eq_zero_iff`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CIVAxisymmetric/Closure/PolarREqZero.lean#L28-L44) — `lean-pool-0039`

Snippet: `samples/lean-pool/lean-pool-0039.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sq_add_sq_eq_zero
- **file**: Mathlib/Algebra/Order/Ring/Unbundled/Basic.lean
- **derivation**: unfold polarR
rw [Real.sqrt_eq_zero (by positivity), sq_add_sq_eq_zero]
- **explanation**: `polarR x` is `√(x 0 ^ 2 + x 1 ^ 2)`. Mathlib's `sq_add_sq_eq_zero` says `a ^ 2 + b ^ 2 = 0 ↔ a = 0 ∧ b = 0` in an ordered ring, which is exactly the algebraic content of the theorem. The only other step is `Real.sqrt_eq_zero` with a nonnegativity side goal, which `positivity` closes. The current proof instead unfolds this by hand with `nlinarith`. I did not open `Real.sqrt_eq_zero` to check its exact statement. I'm assuming it takes `0 ≤ x` and gives `√x = 0 ↔ x = 0`. The derivation above was not compiled.

### [`SteinhausThreeGap.posOrbit_nonempty`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SteinhausThreeGap/Basic.lean#L235-L241) — `lean-pool-0139`

Snippet: `samples/lean-pool/lean-pool-0139.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.Nontrivial.erase_nonempty
- **file**: Mathlib/Data/Finset/Basic.lean
- **derivation**: Finset.Nontrivial.erase_nonempty (Finset.one_lt_card_iff_nontrivial.mp (lt_of_lt_of_le one_lt_two h2))
- **explanation**: posOrbit a N is defined as (orbit a N).erase 0, and orbitCard a N is (orbit a N).card. The hypothesis 2 ≤ card gives s.Nontrivial through Finset.one_lt_card_iff_nontrivial. Mathlib's Finset.Nontrivial.erase_nonempty says that a nontrivial finset s has (s.erase a).Nonempty, for any a. The theorem is that lemma with s := orbit a N and a := 0. The current proof does the same thing by hand: it takes an element different from 0 with Nontrivial.exists_ne and then uses mem_posOrbit_iff. The derivation needs the definitions of posOrbit and orbitCard to unfold, which Lean does by defeq.

### [`BooleanIsoperimetry.CoherentGap.dot_sub`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanIsoperimetry/ConwayGuyCoherentGap.lean#L492-L495) — `lean-pool-0144`

Snippet: `samples/lean-pool/lean-pool-0144.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: sub_dotProduct
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: by simpa [dot, dotProduct] using sub_dotProduct first second weights
- **explanation**: The library's `dot relation weights` is `∑ i, relation i * weights i` on `Fin n → ℤ`. This is definitionally Mathlib's `dotProduct` (`v ⬝ᵥ w`). `sub_dotProduct` states `(u - v) ⬝ᵥ w = u ⬝ᵥ w - v ⬝ᵥ w`. So the theorem is that lemma at `ℤ` and `Fin n`, after unfolding `dot`. I did not check whether `u`, `v`, `w` are explicit in `sub_dotProduct`. If they are implicit, drop the three arguments in the derivation.

### [`Polynomial.eval_comp_X_sub_C_natCast`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Nikodym/Nikodym/LowerBound/Algebra/PolyAsymptotics.lean#L108-L112) — `lean-pool-0148`

Snippet: `samples/lean-pool/lean-pool-0148.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.eval_comp
- **file**: Mathlib/Algebra/Polynomial/Eval/Defs.lean
- **derivation**: by simp [eval_comp, Nat.cast_sub h]
- **explanation**: Mathlib has no `eval_comp_X_sub_C`; the library's own helper of that name (line 105) is a local lemma. The statement follows from `Polynomial.eval_comp` ((p.comp q).eval x = p.eval (q.eval x)). With q = X - C e, `simp` finishes with `eval_sub`, `eval_X` and `eval_C`, and `Nat.cast_sub h` handles the natural-number subtraction cast. No other Mathlib declaration states the shifted-evaluation fact.

### [`gcd_reduction_pos_a_div`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/RamanujanTauMissesPrimes/Solution.lean#L3109-L3111) — `lean-pool-0188`

Snippet: `samples/lean-pool/lean-pool-0188.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Nat.div_gcd_pos_of_pos_left
- **file**: Init/Data/Nat/Gcd.lean
- **derivation**: Nat.div_gcd_pos_of_pos_left b ha
- **explanation**: Lean core's `Nat.div_gcd_pos_of_pos_left (b : Nat) (h : 0 < a) : 0 < a / a.gcd b` is exactly the theorem. The library's proof reaches the same result by another route, using `Nat.div_pos` and `Nat.le_of_dvd`.

### [`NavierStokesR3.LocalizedTensorBounds.continuous_component`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/R3/PressureFlux.lean#L2383-L2385) — `lean-pool-0195`

Snippet: `samples/lean-pool/lean-pool-0195.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PiLp.continuous_apply
- **file**: Mathlib/Analysis/Normed/Lp/PiLp.lean
- **derivation**: (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hf
- **explanation**: `Space` is `EuclideanSpace ℝ (Fin 3)`, which is `PiLp 2 (fun _ : Fin 3 => ℝ)`. Mathlib's `PiLp.continuous_apply` says that `fun f : PiLp p β => f i` is continuous. Composing it with `hf` gives the theorem. The library's proof reaches the same fact by composing `continuous_apply` with `EuclideanSpace.equiv`. So the theorem is a one-line special case: `PiLp.continuous_apply` at p = 2, with `Continuous.comp`.

### [`EulerOrdinaryMollifier.kernel_compact`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/OrdinaryEulerLocalExistence.lean#L644-L644) — `lean-pool-0216`

Snippet: `samples/lean-pool/lean-pool-0216.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContDiffBump.hasCompactSupport_normed
- **file**: Mathlib/Analysis/Calculus/BumpFunction/Normed.lean
- **derivation**: (bump n).hasCompactSupport_normed
- **proof_uses_it**: True
- **explanation**: `kernel n` is defined as `(bump n).normed volume`, where `bump n` is a `ContDiffBump 0`. Mathlib's `ContDiffBump.hasCompactSupport_normed` states `HasCompactSupport (f.normed μ)`. The theorem is that lemma with `f := bump n` and `μ := volume`, after unfolding `kernel`. The library's proof is exactly this application.

### [`QuadraticCarleson.KrauseLaceyShiftedLocalization.krauseLaceyFixedScaleInput_eq_of_support_subset`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuadraticCarleson/QuadraticCarleson/KrauseLaceyShiftedLocalization.lean#L107-L130) — `lean-pool-0222`

Snippet: `samples/lean-pool/lean-pool-0222.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.indicator_biUnion_apply
- **file**: Mathlib/Algebra/BigOperators/Group/Finset/Indicator.lean
- **derivation**: funext x; rw [krauseLaceyFixedScaleInput, ← Finset.indicator_biUnion_apply S _ hdisj, Set.indicator_eq_self.2 hcover]
- **explanation**: The definition is `krauseLaceyFixedScaleInput S f x = ∑ I ∈ S, I.centralThird.indicator f x`. `Finset.indicator_biUnion_apply` (the additive form of `mulIndicator_biUnion_apply`) says that for a finset `s` with `(s : Set ι).PairwiseDisjoint t`, `indicator (⋃ i ∈ s, t i) f x = ∑ i ∈ s, indicator (t i) f x`. `hdisj` is exactly `PairwiseDisjoint` for `t := centralThird`, since `PairwiseDisjoint` unfolds to `Pairwise (Disjoint on t)`. This turns the sum into `indicator (⋃ I ∈ S, I.centralThird) f x`. `Set.indicator_eq_self : s.indicator f = f ↔ support f ⊆ s`, applied to `hcover`, then finishes. The current proof instead does the sum by hand with `Finset.sum_eq_single`. The derivation uses two Mathlib lemmas, so this is a borderline `special_case`, but the glue is trivial.

### [`MarkovProcess.ContinuousPath.denseRestriction_injective`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkovProcess/MarkovProcess/Continuity/DenseTimeContinuousExtension.lean#L55-L62) — `lean-pool-0233`

Snippet: `samples/lean-pool/lean-pool-0233.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: DenseRange.equalizer
- **file**: Mathlib/Topology/DenseEmbedding.lean
- **derivation**: fun omega eta h => ContinuousMap.ext (congrFun (denseRange_castOrderEmbedding.equalizer omega.continuous eta.continuous h))
- **proof_uses_it**: True
- **explanation**: The theorem says a continuous path C(NNReal, alpha) into a T2 space is determined by its values on the dense range of DenseTime.castOrderEmbedding. That is DenseRange.equalizer (two continuous maps into a T2 space that agree after precomposition with a dense-range map are equal), applied with f := castOrderEmbedding, g := omega and h := eta. The rest is ContinuousMap.ext and congrFun glue. Only the final step (ext/congrFun) differs from the library proof, which already uses DenseRange.equalizer. The nearest other Mathlib statement is ContinuousMap.injective_restrict, which covers subtype restriction rather than precomposition with a dense-range map.

### [`AleksandrovDifferentiability.secondOrderDifferentiableAE_iff_measure_secondOrderBadSet_eq_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ViscositySolutionTheory/AleksandrovDifferentiability/Analysis/GoodSet.lean#L314-L321) — `lean-pool-0234`

Snippet: `samples/lean-pool/lean-pool-0234.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.ae_iff
- **file**: Mathlib/MeasureTheory/OuterMeasure/AE.lean
- **derivation**: by rw [SecondOrderDifferentiableAE, ae_iff]; rfl
- **proof_uses_it**: True
- **explanation**: SecondOrderDifferentiableAE μ u is defined as ∀ᵐ x ∂μ, SecondOrderDifferentiableAt u x. Mathlib's `ae_iff` says (∀ᵐ a ∂μ, p a) ↔ μ {a | ¬p a} = 0. With p := SecondOrderDifferentiableAt u, the set {x | ¬ SecondOrderDifferentiableAt u x} is `secondOrderBadSet u` by unfolding (the library's own proof closes this with `rfl`). The theorem is `ae_iff` plus unfolding the library's definitions. The library's proof already uses `ae_iff`.

### [`Feige.CalibratedChain.sum_chainMass_shift`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Feige/ChainCalibration.lean#L60-L68) — `lean-pool-0235`

Snippet: `samples/lean-pool/lean-pool-0235.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.sum_range_sub'
- **file**: Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean
- **derivation**: by simpa [chainMass] using Finset.sum_range_sub' (fun j => K (t + j)) r
- **explanation**: `Finset.sum_range_sub'` is the additive form of `prod_range_div'`. It states `∑ i ∈ range n, (f i - f (i+1)) = f 0 - f n` for an additive commutative group. Take `f j = K (t + j)` and `n = r`. Then `chainMass K (t+j)` unfolds to `K (t+j) - K (t+j+1)`, which matches `f j - f (j+1)` up to `Nat.add_assoc`. The right side `f 0 - f r` becomes `K t - K (t+r)` after `t + 0 = t`. I read the statement in the Mathlib source but could not run Lean, so the `simpa` line is untested. The library's own proof is a direct induction and does not use this lemma.

### [`QuantumQueryComplexity.isSelfAdjoint_chordSq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/QuantumQuery/StateConversion.lean#L407-L410) — `lean-pool-0288`

Snippet: `samples/lean-pool/lean-pool-0288.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsSelfAdjoint.star_mul_self
- **file**: Mathlib/Algebra/Star/SelfAdjoint.lean
- **derivation**: by unfold chordSq; exact IsSelfAdjoint.star_mul_self (1 - U)
- **explanation**: chordSq U is defined as (1 - U)ᴴ * (1 - U). In Mathlib, star x for a matrix is x.conjTranspose (defeq, Matrix.star_eq_conjTranspose is rfl). IsSelfAdjoint.star_mul_self x : IsSelfAdjoint (star x * x) holds for any StarMul, and matrices over ℂ have that instance. Taking x = 1 - U gives the result after unfolding chordSq. I did not read the library's own proof of chordSq_conjTranspose, so I have not checked that this route is independent of it.

### [`EulerPacketInductionScales.Scales.support_pos`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/PacketInductionScaleBounds.lean#L53-L53) — `lean-pool-0308`

Snippet: `samples/lean-pool/lean-pool-0308.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.exp_pos
- **file**: Mathlib/Analysis/SpecialFunctions/Exp.lean
- **derivation**: Real.exp_pos _
- **proof_uses_it**: True
- **explanation**: `supportScale J X n` is defined as `exp (-scaleSequence J X n / ((J+n : ℕ) : ℝ)^(7/2))`, so the statement is `0 < Real.exp _` after unfolding the definition. That is `Real.exp_pos` applied to the argument. The current proof is exactly `exp_pos _`. I did not open the file that declares `Real.exp_pos`; the path is from memory, and the declaration itself is standard Mathlib.

### [`Surreal.rationalTailQuotient_abs`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConwayRefinement/ConwayRefinement/Surreal/RationalTailQuotient.lean#L73-L85) — `lean-pool-0330`

Snippet: `samples/lean-pool/lean-pool-0330.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: map_abs
- **file**: Mathlib/Algebra/Order/Group/Unbundled/Abs.lean
- **derivation**: exact (map_abs (⟨QuotientAddGroup.mk' _, fun _ _ h ↦ ConvexQuotient.mk_le_mk h⟩ : Surreal.{u} →+o RationalTailQuotient T) x).symm
- **explanation**: The theorem says that the quotient map from Surreal to RationalTailQuotient T commutes with absolute value. Mathlib's `map_mabs` (additive form `map_abs`) states `f |a| = |f a|` for any `f` with `[OrderHomClass F α β] [MonoidHomClass F α β]` (the additive form uses `AddMonoidHomClass`), over a linear order on the target. The quotient map is a monotone additive homomorphism, so it is an `OrderAddMonoidHom` (`→+o`), built with the library's `ConvexQuotient.mk_le_mk` as the monotonicity proof. Applying `map_abs` to it gives `mk |x| = |mk x|`, which is the claim with the two sides swapped. The derivation needs this `→+o` structure to be built; Mathlib has no `OrderHomClass` instance for the bare quotient map. The existing proof does not use `map_abs`: it splits into the cases `0 ≤ x` and `x ≤ 0` and applies `abs_of_nonneg` and `abs_of_nonpos`. I did not compile the derivation. The defeq between `Submodule.Quotient.mk x` and `QuotientAddGroup.mk' _ x` is already used at line 101 of the same file.

### [`EulerCylinderMollifier.mollifierKernel_integral`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/Foundations/CylinderMollifier.lean#L95-L96) — `lean-pool-0333`

Snippet: `samples/lean-pool/lean-pool-0333.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ContDiffBump.integral_normed
- **file**: Mathlib/Analysis/Calculus/BumpFunction/Normed.lean
- **derivation**: (mollifierBump n).integral_normed
- **proof_uses_it**: True
- **explanation**: mollifierKernel n is defined as (mollifierBump n).normed volume. Mathlib's ContDiffBump.integral_normed states ∫ x, f.normed μ x ∂μ = 1 for a general bump f and measure μ. The theorem is this lemma instantiated at the library's bump function and volume. The library's proof is already this single application.

### [`LeanStationaryHarmonicMaps.StationaryHarmonicMap.deriv_thetaFactor`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanStationaryHarmonicMaps/StationaryHarmonicMap/EnergyQuantities.lean#L103-L112) — `lean-pool-0370`

Snippet: `samples/lean-pool/lean-pool-0370.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: deriv_zpow
- **file**: Mathlib/Analysis/Calculus/Deriv/ZPow.lean
- **derivation**: unfold thetaFactor
rw [deriv_zpow, show (2 - (n : ℤ)) - 1 = 1 - (n : ℤ) by omega]; push_cast; rfl
- **proof_uses_it**: True
- **explanation**: thetaFactor n r = r ^ (2 - (n:ℤ)). Mathlib's deriv_zpow (m : ℤ) (x : 𝕜) says deriv (fun x => x ^ m) x = m * x ^ (m - 1). Taking 𝕜 = ℝ and m = 2 - n gives the statement, apart from a cast push (↑(2 - n) = 2 - ↑n) and rewriting the exponent (2 - n) - 1 = 1 - n. The current proof already uses deriv_zpow and adds only those two small facts, so this is a specialization with routine glue.

### [`EllipticPdes.Extension.stepProfile_le_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EllipticPDE/Extension/Cutoff.lean#L62-L62) — `lean-pool-0373`

Snippet: `samples/lean-pool/lean-pool-0373.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.smoothTransition.le_one
- **file**: Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean
- **derivation**: Real.smoothTransition.le_one _
- **proof_uses_it**: True
- **explanation**: stepProfile t is defined as Real.smoothTransition (t - 1). Mathlib's `Real.smoothTransition.le_one` states `smoothTransition x ≤ 1` for every real x. Instantiating x := t - 1 and unfolding `stepProfile` gives the theorem, and the library's proof does exactly that.

### [`Nat.gt_and_neq_succ_gt_succ`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MRiscX/Util/BasicTheorems.lean#L68-L70) — `lean-pool-0409`

Snippet: `samples/lean-pool/lean-pool-0409.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.lt_of_le_of_ne
- **file**: Init/Prelude.lean
- **derivation**: fun n m h₁ h₂ => Nat.lt_of_le_of_ne h₁ (Ne.symm h₂)
- **explanation**: Nat.lt_of_le_of_ne {n m : Nat} (h₁ : n ≤ m) (h₂ : ¬ n = m) : n < m. Instantiating n := n+1, m := m gives n+1 < m from n+1 ≤ m and n+1 ≠ m. The hypothesis n < m is definitionally n+1 ≤ m (Nat.lt n m := Nat.le (n+1) m). The hypothesis m ≠ n+1 is flipped with Ne.symm. The library proves it with grind instead. If the defeq doesn't elaborate directly, use `Nat.succ_le_of_lt h₁` in place of h₁.

### [`BollobasNikiforov.euclid_sq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BollobasNikiforov/M/HalfPlane.lean#L59-L60) — `lean-pool-0416`

Snippet: `samples/lean-pool/lean-pool-0416.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.sq_sqrt
- **file**: Mathlib/Analysis/Real/Sqrt.lean
- **derivation**: Real.sq_sqrt (by simpa using dotProduct_star_self_nonneg w)
- **proof_uses_it**: True
- **explanation**: `euclid w` is defined as `Real.sqrt (w ⬝ᵥ w)`. After unfolding it, the statement is `√x ^ 2 = x` with `x = w ⬝ᵥ w`. That is `Real.sq_sqrt (h : 0 ≤ x) : √x ^ 2 = x`. The library's proof already applies `Real.sq_sqrt`. The nonnegativity side goal is `dotProduct_star_self_nonneg` (Mathlib/LinearAlgebra/Matrix/DotProduct.lean, `0 ≤ star v ⬝ᵥ v`), because `star` is trivial on ℝ. I did not check that `simpa` closes this goal. The library's own `euclid_inner_nonneg` also works.

### [`EulerLpBochnerRealization.realization_ae`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/LpBochnerRealization.lean#L77-L81) — `lean-pool-0430`

Snippet: `samples/lean-pool/lean-pool-0430.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.MemLp.coeFn_toLp
- **file**: Mathlib/MeasureTheory/Function/LpSpace/Basic.lean
- **derivation**: (field_memLp w f hf hrep).coeFn_toLp
- **proof_uses_it**: True
- **explanation**: `realization w f hf hrep` is by definition `(field_memLp w f hf hrep).toLp f`. The theorem says its coercion is a.e. equal to `f`. That is `MemLp.coeFn_toLp` (`hf.toLp f =ᵐ[μ] f`) with the measure `μ.prod ν` and the membership proof `field_memLp ...`. The only step beyond Mathlib is unfolding the definition `realization`.

### [`CKN.vlConv_apply_swap`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/Support/VorticityLocalizedEnergyWeakTime.lean#L78-L81) — `lean-pool-0443`

Snippet: `samples/lean-pool/lean-pool-0443.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: convolution_lsmul_swap
- **file**: Mathlib/Analysis/Convolution.lean
- **derivation**: by rw [vlConv, convolution_lsmul_swap]; simp [mul_comm]
- **explanation**: vlConv k h is by definition `convolution k h (lsmul ℝ ℝ) volume`. Mathlib's `convolution_lsmul_swap` (and the more general `convolution_eq_swap`, which the current proof uses) gives `(f ⋆[lsmul 𝕜 𝕜, μ] g) x = ∫ t, f (x - t) • g t ∂μ`. Instantiating with 𝕜 = ℝ, F = ℝ, μ = volume and rewriting `smul_eq_mul` and `mul_comm` gives the stated `∫ y, h y * k (x - y)`. The current proof applies the more general `convolution_eq_swap`, not `convolution_lsmul_swap`.

### [`AVenhance.FaaDiBruno.Product.harmonicOne_sq_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/FaaDiBruno/Product.lean#L293-L297) — `lean-pool-0462`

Snippet: `samples/lean-pool/lean-pool-0462.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.sum_mul_sq_le_sq_mul_sq
- **file**: Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean
- **derivation**: simpa [Product.harmonicOne, Product.harmonicTwo] using
  Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun _ : ℕ ↦ (1 : ℝ)) (fun k ↦ (k + 1 : ℝ)⁻¹)
- **proof_uses_it**: True
- **explanation**: harmonicOne m = ∑_{k<m} (k+1)⁻¹ and harmonicTwo m = ∑_{k<m} ((k+1)^2)⁻¹. Cauchy–Schwarz (∑ f g)^2 ≤ (∑ f^2)(∑ g^2), with f = 1 and g k = (k+1)⁻¹ over Finset.range m, gives (harmonicOne m)^2 ≤ m * harmonicTwo m. The `simpa` step only unfolds the two definitions and simplifies 1^2 sums to the cardinality m. I found no Mathlib lemma about squared harmonic sums in ℝ, so the match is the general Cauchy–Schwarz lemma.

### [`BeyondBethe.machineRationalVectorSub_done_iterate`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BeyondBethe/BeyondBethe/MachineRationalVectorSub.lean#L520-L529) — `lean-pool-0471`

Snippet: `samples/lean-pool/lean-pool-0471.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Function.iterate_fixed
- **file**: Mathlib/Logic/Function/Iterate.lean
- **derivation**: exact Function.iterate_fixed (by simp [machineRationalVectorSubStep]) extra
- **explanation**: Mathlib's `Function.iterate_fixed {x} (h : f x = x) (n : ℕ) : f^[n] x = x` is the same statement with f := machineRationalVectorSubStep and x := the packed done state. The theorem's current proof is an induction that redoes this, and its inductive step already uses the same `simp [machineRationalVectorSubStep]` for the one-step fixed-point fact. That fact is the only library-specific part, and the derivation closes it with `simp`.

### [`CKN.Leray.integrable_mul_reflect`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegLocalEnergyBound.lean#L99-L101) — `lean-pool-0495`

Snippet: `samples/lean-pool/lean-pool-0495.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HasCompactSupport.convolutionExists_right
- **file**: Mathlib/Analysis/Convolution.lean
- **derivation**: exact (hκc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) (hg.locallyIntegrable (by norm_num)) hκ) x
- **explanation**: Mathlib's `HasCompactSupport.convolutionExists_right` says that a locally integrable f and a continuous compactly supported g have `ConvolutionExists f g L μ`. This unfolds to `Integrable (fun t => L (f t) (g (x - t)))` for every x. With L = `ContinuousLinearMap.mul ℝ ℝ`, f = g, and g = κ, this is the target statement. `MemLp.locallyIntegrable` gives local integrability of g from `MemLp g 2`. The library's own proof instead uses `MemLp.integrable_mul` (Hölder) together with its own `memLp_reflect`. I did not read the context's instance setup (Vec3, volume), so I did not confirm that Mathlib's group and measure instance requirements hold there. I also did not confirm that the `ConvolutionExists` unfolding closes by `rfl`.

### [`Matrix.unitaryGroup.coe_hMul_star_self`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/LinearAlgebra/InnerAut.lean#L139-L142) — `lean-pool-0499`

Snippet: `samples/lean-pool/lean-pool-0499.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: unitary.coe_mul_star_self
- **file**: Mathlib/Algebra/Star/Unitary.lean
- **derivation**: exact unitary.coe_mul_star_self a
- **explanation**: Mathlib's `unitary.coe_mul_star_self (U : unitary R) : (U : R) * star U = 1` is stated for any monoid with star-mul structure `R`. `Matrix.unitaryGroup n α` is an abbrev for `unitary (Matrix n n α)`, so the theorem is the case `R = Matrix n n 𝕜`. The coercion of `star a` to a matrix is `star ↑a` by `unitary.coe_star` (rfl), so the two statements agree. The library proves it with `simp_all` and does not cite the Mathlib lemma.

### [`NRR.Geometry.upperClosedHalfspace_convex`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NandakumarRamanaRao/NRR/Geometry/ConvexBody/HalfspaceCut.lean#L91-L99) — `lean-pool-0523`

Snippet: `samples/lean-pool/lean-pool-0523.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: convex_halfSpace_ge
- **file**: Mathlib/Analysis/Convex/Basic.lean
- **derivation**: convex_halfSpace_ge (f := fun x => inner ℝ u x) ⟨fun x y => inner_add_right u x y, fun c x => inner_smul_right u x c⟩ t
- **explanation**: The set upperClosedHalfspace u t is {x | t ≤ inner ℝ u x}. Mathlib's `convex_halfSpace_ge` says that for a linear map f, {w | r ≤ f w} is convex. Taking f = fun x => inner ℝ u x gives the result. Linearity of f comes from `inner_add_right` and `inner_smul_right`, which are the two fields of `IsLinearMap`. The ordered-module hypotheses on the codomain hold for ℝ. The definition unfolds by `Iff.rfl`, as `mem_upperClosedHalfspace` shows. I did not find a Mathlib lemma for inner products specifically, so this is a specialization of the general lemma.

### [`TauCeti.DavisKahan.ExactSinTheta.sharp52_two_le_sqrt_ten`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/DavisKahan/DavisKahan/Sources/DavisKahan1970/Sylvester/OperatorNormEstimate.lean#L220-L222) — `lean-pool-0525`

Snippet: `samples/lean-pool/lean-pool-0525.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.le_sqrt_of_sq_le
- **file**: Mathlib/Analysis/Real/Sqrt.lean
- **derivation**: Real.le_sqrt_of_sq_le (by norm_num)
- **explanation**: Real.le_sqrt_of_sq_le (h : x ^ 2 ≤ y) : x ≤ √y. Taking x = 2 and y = 10 leaves the side goal (2:ℝ)^2 ≤ 10, which norm_num closes. The library's proof uses nlinarith with Real.sq_sqrt instead.

### [`CK.mul'_π`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConnesKreimer/Core.lean#L1694-L1700) — `lean-pool-0540`

Snippet: `samples/lean-pool/lean-pool-0540.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: AlgHom.comp_mul'
- **file**: Mathlib/Algebra/Algebra/Bilinear.lean
- **derivation**: exact (AlgHom.comp_mul' (π k)).symm
- **explanation**: Mathlib's `AlgHom.comp_mul'` says that for an algebra hom f : A →ₐ B, `f.toLinearMap ∘ₗ μ = μ[R] ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap)`. Here `μ` is `LinearMap.mul' R A`, and `⊗ₘ` is `TensorProduct.map`. Taking f := π k : H k →ₐ[k] Hab k gives the target statement with the two sides swapped. The library's proof uses `TensorProduct.ext'` and `simp_all` instead. I did not check that the `CommRing (Hab k)` instance agrees with the RingQuot semiring structure by unification. I expect it does, since π is an AlgHom into `Hab k` and the statement type-checks.

### [`Zeta32.Arith.Local.zmod_eq_iff_dvd`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta32/Arith/Local/PoleFun.lean#L41-L43) — `lean-pool-0553`

Snippet: `samples/lean-pool/lean-pool-0553.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ZMod.intCast_eq_intCast_iff_dvd_sub
- **file**: Mathlib/Data/ZMod/Basic.lean
- **derivation**: by rw [eq_comm]; exact ZMod.intCast_eq_intCast_iff_dvd_sub b a p
- **explanation**: Mathlib states `(a : ZMod c) = b ↔ (c : ℤ) ∣ b - a`. The theorem has `a - b` in the divisibility, so the two statements differ by swapping a and b. Taking `eq_comm` first and then applying the Mathlib lemma with a and b swapped, and c := p, gives exactly the theorem. The current proof goes through `ZMod.intCast_zmod_eq_zero_iff_dvd` instead.

### [`BollobasNikiforov.continuous_vecMulVec_self`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BollobasNikiforov/CP/Closed.lean#L51-L54) — `lean-pool-0578`

Snippet: `samples/lean-pool/lean-pool-0578.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Continuous.matrix_vecMulVec
- **file**: Mathlib/Topology/Instances/Matrix.lean
- **derivation**: continuous_id.matrix_vecMulVec continuous_id
- **proof_uses_it**: True
- **explanation**: Mathlib's `Continuous.matrix_vecMulVec` says that if A, B : X → m → R are continuous, then x ↦ vecMulVec (A x) (B x) is continuous. Taking X = (n → ℝ), R = ℝ and A = B = id gives the theorem, and the library's proof is exactly that one line.

### [`Real.exists_eq_of_iSup_eq_of_finite_domain`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/WhiteheadTheorem/Auxiliary.lean#L96-L110) — `lean-pool-0599`

Snippet: `samples/lean-pool/lean-pool-0599.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: exists_eq_ciSup_of_finite
- **file**: Mathlib/Order/ConditionallyCompleteLattice/Finset.lean
- **derivation**: haveI : Nonempty ι := hfz.nonempty
obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := f); exact ⟨i, hi.trans hf⟩
- **explanation**: Mathlib's `exists_eq_ciSup_of_finite` says that for a finite nonempty index type and `f : ι → α` in a conditionally complete linear order, `∃ i, f i = ⨆ i, f i`. The theorem is this lemma at `α = ℝ`. The only extra step is getting `Nonempty ι` from `hfz` and rewriting with `hf : ⨆ i, f i = a`. The hypothesis `∃ i, f i ≥ 0` is used only for nonemptiness. I read the Mathlib statement, but I did not check the lemma's variable and instance setup beyond its signature.

### [`EllipticPdes.Extension.stepProfile_eq_one`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EllipticPDE/Extension/Cutoff.lean#L57-L58) — `lean-pool-0610`

Snippet: `samples/lean-pool/lean-pool-0610.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Real.smoothTransition.one_of_one_le
- **file**: Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean
- **derivation**: Real.smoothTransition.one_of_one_le (by linarith)
- **proof_uses_it**: True
- **explanation**: stepProfile t is defined as Real.smoothTransition (t - 1). Mathlib's `Real.smoothTransition.one_of_one_le (h : 1 ≤ x) : smoothTransition x = 1` gives the result once the definition is unfolded and x := t - 1. The side goal 1 ≤ t - 1 follows from 2 ≤ t by linarith. The library's proof is exactly this one-liner.

### [`CKN.Core.Step4.min_kappa_pos`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Core/Step4/KappaCapArithmetic.lean#L57-L62) — `lean-pool-0622`

Snippet: `samples/lean-pool/lean-pool-0622.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: lt_min
- **file**: Mathlib/Order/Defs/LinearOrder.lean
- **derivation**: lt_min (by positivity) hq
- **proof_uses_it**: True
- **explanation**: The statement is `lt_min : a < b → a < c → a < min b c` with a = 0, b = (1/τ + 8/25)⁻¹, c = q on ℝ. The first hypothesis, positivity of (1/τ + 8/25)⁻¹, is a routine side goal that `positivity` closes using hτ. The second hypothesis is hq. The current proof already applies `lt_min`. I found no Mathlib lemma that states this specific expression.

### [`Subtype.val_comp_single`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BruhatTits/Utils/Subring.lean#L24-L28) — `lean-pool-0654`

Snippet: `samples/lean-pool/lean-pool-0654.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Pi.single_op
- **file**: Mathlib/Algebra/Notation/Pi/Basic.lean
- **derivation**: (Pi.single_op (fun _ => Subtype.val) (fun _ => rfl) i a).symm
- **explanation**: Pi.single_op (additive form of Pi.mulSingle_op) states Pi.single i (op i x) = fun j => op j (Pi.single i x j) for op : ∀ i, M i → N i with op i 0 = 0. Taking op := fun _ => Subtype.val (zero preserved by rfl) gives Pi.single i (a : R) = Subtype.val ∘ Pi.single i a, which is the target's statement with the sides swapped. The pointwise version Pi.apply_single also exists. The current proof uses ext and aesop. I read the statement but could not run Lean, so I haven't confirmed that the derivation elaborates.

### [`RS.Cech.H1.induction_on`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/Cech/Colimit.lean#L112-L115) — `lean-pool-0668`

Snippet: `samples/lean-pool/lean-pool-0668.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Module.DirectLimit.induction_on
- **file**: Mathlib/Algebra/Colimit/Module.lean
- **derivation**: Module.DirectLimit.induction_on ξ ih
- **proof_uses_it**: True
- **explanation**: `H1 D` is an `abbrev` for `Module.DirectLimit (fun 𝒰 => H1Cover D 𝒰) (fun _ _ h => resH1' D h)`, and `toH1 D 𝒰` is defined as `Module.DirectLimit.of ℂ _ _ _ 𝒰`. The theorem is Mathlib's `Module.DirectLimit.induction_on` instantiated at this particular directed system, and the library's proof is exactly that term. The `Nonempty` and `IsDirectedOrder` instances on `FinCover` are supplied elsewhere in the library.

### [`lmul_eq_zero_iff`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/LinearAlgebra/LmulRmul.lean#L152-L154) — `lean-pool-0683`

Snippet: `samples/lean-pool/lean-pool-0683.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: LinearMap.mulLeft_eq_zero_iff
- **file**: Mathlib/Algebra/Module/LinearMap/Basic.lean
- **derivation**: LinearMap.mulLeft_eq_zero_iff _ _ _
- **proof_uses_it**: True
- **explanation**: `lmul x` is defined as `LinearMap.mulLeft R x`. Mathlib's `LinearMap.mulLeft_eq_zero_iff (a : A) : mulLeft R a = 0 ↔ a = 0` is the same statement once `lmul` is unfolded. The library's proof applies it directly.

### [`dist_le_integral_of_norm_deriv_le_of_le`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/SardMoreira/ToMathlib/PR32186.lean#L28-L60) — `lean-pool-0702`

Snippet: `samples/lean-pool/lean-pool-0702.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: norm_sub_le_integral_of_norm_deriv_le_of_le
- **file**: Mathlib/MeasureTheory/Integral/IntervalIntegral/DistLEIntegral.lean
- **derivation**: by rw [dist_eq_norm_sub']; exact norm_sub_le_integral_of_norm_deriv_le_of_le hab hfc hfd hfB hBi
- **explanation**: Mathlib's `norm_sub_le_integral_of_norm_deriv_le_of_le` has exactly the same hypotheses (hab, hfc, hfd, hfB, hBi). Its conclusion is `‖f b - f a‖ ≤ ∫ t in a..b, B t`. The theorem's conclusion is `dist (f a) (f b) ≤ ∫ ...`. These differ only by `dist_eq_norm_sub'`, which rewrites `dist (f a) (f b)` as `‖f b - f a‖`. The library's proof is a copy of Mathlib's proof, with the extra `dist_eq_norm_sub'` rewrite.

### [`TriangleInflation.Graph.Sound.empty_fun_eq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/InflationTermination/TriangleInflation/Graph/Soundness.lean#L580-L581) — `lean-pool-0711`

Snippet: `samples/lean-pool/lean-pool-0711.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Pi.uniqueOfIsEmpty
- **file**: Mathlib/Basic/Unique.lean
- **derivation**: Subsingleton.elim f g
- **explanation**: Mathlib has `instance Pi.uniqueOfIsEmpty [IsEmpty α] (β : α → Sort v) : Unique (∀ a, β a)` and `Finset.instIsEmpty : IsEmpty (∅ : Finset α)`. Together they give `Unique (↥(∅ : Finset (GObs Γ t)) → Bool)`, so `Subsingleton.elim f g` proves the statement. The theorem's own proof uses `funext` and `Finset.notMem_empty` instead.

### [`Chudnovsky.modularForm_SL_smul`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Chudnovsky/SingularModuli/JFunction.lean#L80-L89) — `lean-pool-0725`

Snippet: `samples/lean-pool/lean-pool-0725.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SlashInvariantForm.slash_action_eqn''
- **file**: Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean
- **derivation**: exact SlashInvariantForm.slash_action_eqn'' f (γ := (γ : GL (Fin 2) ℝ)) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩) τ
- **explanation**: Mathlib's `SlashInvariantForm.slash_action_eqn''` states that for any `[SlashInvariantFormClass F Γ k]` with `Γ.HasDetOne`, `γ ∈ Γ` gives `f (γ • z) = (denom γ z)^k * f z`. Take `Γ = 𝒮ℒ`, the range of `SL(2,ℤ) → GL(2,ℝ)`, which has `HasDetOne`. A modular form of level `𝒮ℒ` is a `SlashInvariantFormClass` instance. Membership of `γ` is `MonoidHom.mem_range.mpr ⟨γ, rfl⟩`, the same step the library's proof already uses. The related `slash_action_eqn_SL''` is stated for subgroups of `SL(2,ℤ)`, and `LevelOne/Basic.lean` converts `𝒮ℒ` to `Γ(1)` to use it. The library's proof rederives the result from `slash_action_eq'` by hand. I did not check that the coercions of `γ` and the `•` actions line up definitionally, so the derivation may need a small `simpa` adjustment.

### [`AVenhance.Infra.Section5.Contracts.sd_spaceGrad_add`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Section5/Contracts/TermCenteredSplitCalculus.lean#L27-L32) — `lean-pool-0736`

Snippet: `samples/lean-pool/lean-pool-0736.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: fderiv_fun_add
- **file**: Mathlib/Analysis/Calculus/FDeriv/Add.lean
- **derivation**: by simp only [spaceGrad]; rw [fderiv_fun_add hf hg]; rfl
- **proof_uses_it**: True
- **explanation**: I did not open Mathlib's `fderiv_fun_add`. I know it only from the library's own proof, which calls it. `spaceGrad f x i` is defined as `fderiv ℝ f x (basisVec i)`. The theorem is therefore additivity of `fderiv` at a point where both functions are differentiable, evaluated at a basis vector. The only other steps are unfolding `spaceGrad` and a closing `rfl`. No Mathlib declaration mentions `spaceGrad`, so I judged this a special case of `fderiv_fun_add` rather than a duplicate.

### [`Homogenization.cubeBoundaryLayer_subset_cubeSet`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/Homogenization/Geometry/BoundaryLayer.lean#L69-L71) — `lean-pool-0742`

Snippet: `samples/lean-pool/lean-pool-0742.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.sdiff_subset
- **file**: Mathlib/Order/BooleanAlgebra/Set.lean
- **derivation**: Set.sdiff_subset
- **proof_uses_it**: True
- **explanation**: cubeBoundaryLayer Q t is defined as cubeSet Q \ cubeShrunkSet Q t, so the statement is the instance of `Set.sdiff_subset : s \ t ⊆ s` with s := cubeSet Q and t := cubeShrunkSet Q t. The current proof is exactly this lemma, with the definition unfolded.

### [`UnrestrictedBooleanMul.N4.f2_mul_self_quartic`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/BooleanMultiplication/N4/QuarticLowLow.lean#L30-L31) — `lean-pool-0767`

Snippet: `samples/lean-pool/lean-pool-0767.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ZMod.pow_card
- **file**: Mathlib/FieldTheory/Finite/Basic.lean
- **derivation**: by rw [← sq]; exact ZMod.pow_card (p := 2) u
- **explanation**: F₂ is defined as `abbrev F₂ := ZMod 2`. Mathlib's `ZMod.pow_card (x : ZMod p) : x ^ p = x` (with `[Fact p.Prime]`) at p = 2 gives `u ^ 2 = u`. Rewriting `u * u` as `u ^ 2` with `sq` yields the theorem. The `Fact (Nat.Prime 2)` instance is `Nat.fact_prime_two`. The library's proof instead case-splits with `f2_eq_zero_or_one` and uses `simp`. I searched Mathlib for `BooleanRing` instances on `ZMod 2` and for `mul_self_eq_self`-style lemmas and found nothing more direct.

### [`FelsConjectureProof.binomial_sum_eq_add_pow`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/FelConjecture/Solution.lean#L1950-L1955) — `lean-pool-0770`

Snippet: `samples/lean-pool/lean-pool-0770.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: add_pow
- **file**: Mathlib/Data/Nat/Choose/Sum.lean
- **derivation**: rw [add_pow]; exact Finset.sum_congr rfl fun k _ => by ring
- **proof_uses_it**: True
- **explanation**: Mathlib's `add_pow` (CommSemiring R) states (x + y)^n = ∑ m ∈ range (n+1), x^m * y^(n-m) * n.choose m. The target is this with R = ℚ, x = a, y = b, symmetry swapped, and each summand's factors reordered (choose * a^k * b^(n-k) instead of a^k * b^(n-k) * choose). The reordering is closed by `ring` termwise, so the target follows from `add_pow` by instantiation plus routine glue. The current proof is this same derivation. I found no declaration with the exact factor order.

### [`pentagonal_injective''`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/PentagonalNumberTheorem/Old.lean#L68-L73) — `lean-pool-0779`

Snippet: `samples/lean-pool/lean-pool-0779.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: pentagonal_injective
- **file**: Mathlib/Combinatorics/Enumerative/Pentagonal/Basic.lean
- **derivation**: intro a b h
exact pentagonal_injective (by simpa [pentagonal'', ← natCast_pentagonal] using h)
- **explanation**: Mathlib defines `pentagonal : ℤ → ℕ` as `(k * (3 * k - 1) / 2).toNat`, and `natCast_pentagonal` says `(pentagonal k : ℤ) = k * (3 * k - 1) / 2`. The library's `pentagonal'' k = k * (3 * k - 1) / 2` is therefore the ℤ-valued cast of Mathlib's `pentagonal`. `Pentagonal.Basic` has `pentagonal_injective : Function.Injective pentagonal`. Injectivity of `pentagonal''` follows from it by rewriting with `natCast_pentagonal` and cancelling the injective `Nat.cast`. I could not run Lean, so the `simpa` call is untested. Mathlib's own proof of `pentagonal_injective` is independent of the library's theorem.

### [`TriangleInflation.Graph.swapTwist_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/InflationTermination/TriangleInflation/Graph/DoubleStar.lean#L317-L318) — `lean-pool-0781`

Snippet: `samples/lean-pool/lean-pool-0781.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Equiv.swap_apply_left
- **file**: Mathlib/Logic/Equiv/Basic.lean
- **derivation**: Equiv.swap_apply_left 0 (j e)
- **proof_uses_it**: True
- **explanation**: `swapTwist j e` unfolds to `Equiv.swap 0 (j e)`. The theorem is then `Equiv.swap_apply_left a b : swap a b a = b` with `a = 0` and `b = j e`. The library's proof already applies this lemma. I did not open the Mathlib file or check the lemma's exact path, so the file path is a guess.

### [`Polynomial.shiftedLegendre_poly_eval_zero_eq_zero`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Zeta3Irrational/LegendrePoly.lean#L342-L359) — `lean-pool-0784`

Snippet: `samples/lean-pool/lean-pool-0784.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd
- **file**: Mathlib/Algebra/Polynomial/Derivative.lean
- **derivation**: have := (dvd_pow_self X (by omega : n - m ≠ 0)).trans (pow_sub_dvd_iterate_derivative_of_pow_dvd m (dvd_mul_right (X ^ n) ((1 - X) ^ n)))
simpa [← coeff_zero_eq_eval_zero] using X_dvd_iff.mp this
- **explanation**: Mathlib has `pow_sub_dvd_iterate_derivative_of_pow_dvd : q ^ n ∣ p → q ^ (n - m) ∣ derivative^[m] p`. Take q = X, p = X^n * (1-X)^n. Then X^(n-m) divides the m-th derivative, and n-m > 0 because m < n, so X divides it. X ∣ f is equivalent to f.coeff 0 = 0, which is eval 0 f = 0 (`X_dvd_iff`, `coeff_zero_eq_eval_zero`). The library's proof instead expands with the Leibniz rule (`iterate_derivative_mul`) and checks each summand. The derivation is a bit longer than a one-line glue step, so this is borderline. A second route goes through `isRoot_iterate_derivative_of_lt_rootMultiplicity`, but it needs a root-multiplicity bound.

### [`ESS.spatialDeriv_eq_zero_of_notMem_tsupport`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Endpoint/LocalDivCurlCutoff.lean#L46-L49) — `lean-pool-0802`

Snippet: `samples/lean-pool/lean-pool-0802.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: fderiv_of_notMem_tsupport
- **file**: Mathlib/Analysis/Calculus/FDeriv/Const.lean
- **derivation**: by simp [spatialDeriv, fderiv_of_notMem_tsupport ℝ hx]
- **explanation**: `spatialDeriv g i x` unfolds to `(fderiv ℝ g x) (basisVec i)`. Mathlib's `fderiv_of_notMem_tsupport (h : x ∉ tsupport f) : fderiv 𝕜 f x = 0` gives `fderiv ℝ g x = 0`, so the result is `0 (basisVec i) = 0`, which `simp` closes. The library's proof reaches the same fact another way, through `image_eq_zero_of_notMem_tsupport` and `tsupport_fderiv_apply_subset`. I did not find a Mathlib lemma that states the directional-derivative form directly.

### [`Model.Field.ringChar_eq_of_Prime`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EcTateLean/Algebra/EllipticCurve/Model.lean#L508-L517) — `lean-pool-0813`

Snippet: `samples/lean-pool/lean-pool-0813.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CharP.ringChar_of_prime_eq_zero
- **file**: Mathlib/Algebra/CharP/Basic.lean
- **derivation**: CharP.ringChar_of_prime_eq_zero hnp (by simpa using hn)
- **explanation**: Mathlib's `CharP.ringChar_of_prime_eq_zero` says: for a nontrivial non-associative semiring R, a prime p with `(p : R) = 0` gives `ringChar R = p`. The target is the same statement for a field K (nontrivial), with the hypothesis written as `OfNat.ofNat n = 0` instead of `(n : K) = 0`. The two forms are related by `Nat.cast_ofNat`, so `simpa` closes the cast side goal. The library's proof does not use this lemma. It redoes the argument by hand.

### [`CompactSelfAdjoint.exists_reApplyInnerSelf_ne_zero_of_isSelfAdjoint`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CompactSpectral/Analysis/InnerProductSpace/RayleighCompact.lean#L296-L332) — `lean-pool-0854`

Snippet: `samples/lean-pool/lean-pool-0854.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.IsSymmetric.inner_map_self_eq_zero
- **file**: Mathlib/Analysis/InnerProductSpace/Symmetric.lean
- **derivation**: by_contra h; push Not at h
exact h0 (ContinuousLinearMap.coe_injective (by simpa using hT.isSymmetric.inner_map_self_eq_zero.mp fun x => by simpa [h x] using (LinearMap.IsSymmetric.coe_reApplyInnerSelf_apply hT.isSymmetric x).symm))
- **explanation**: The theorem says that a nonzero self-adjoint continuous operator T has some x with re⟪T x, x⟫ ≠ 0. This is the contrapositive of Mathlib's `LinearMap.IsSymmetric.inner_map_self_eq_zero`: for a symmetric linear map, (∀ x, ⟪T x, x⟫ = 0) ↔ T = 0. The only extra step is converting `reApplyInnerSelf` to the inner product. `LinearMap.IsSymmetric.coe_reApplyInnerSelf_apply` does that: (T.reApplyInnerSelf x : 𝕜) = ⟪T x, x⟫. `IsSelfAdjoint.isSymmetric` gives symmetry, as in the library's proof. The library's proof redoes the polarization argument by hand instead of calling the lemma. The derivation is about two lines but I haven't compiled it, so the simp steps may need small adjustments. I searched for `inner_map_self_eq_zero` and `reApplyInnerSelf` in Mathlib. I found no lemma that states the target directly.

### [`HahnSeries.exists_max_mem_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/ConwayRefinement/ConwayRefinement/HahnSeries/EPrimitive.lean#L99-L109) — `lean-pool-0877`

Snippet: `samples/lean-pool/lean-pool-0877.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.exists_max_image
- **file**: Mathlib/Data/Set/Finite/Lemmas.lean
- **derivation**: Set.exists_max_image x.support id hfin (HahnSeries.support_nonempty_iff.mpr hx)
- **explanation**: Set.exists_max_image is generated by `to_dual` from `Set.exists_min_image`. Its statement is `theorem Set.exists_max_image [LinearOrder β] (s : Set α) (f : α → β) (h1 : s.Finite) : s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a`. I did not read the generated declaration directly. I inferred it from the `@[to_dual]` attribute on `exists_min_image` and from a use in `Mathlib/Order/Filter/AtTopBot/Finite.lean`. Taking s = x.support and f = id gives the goal, because `id g ≤ id a` is defeq to `g ≤ a`. Nonemptiness of the support comes from `HahnSeries.support_nonempty_iff : x.support.Nonempty ↔ x ≠ 0`. The current proof does the same thing by hand: it goes through `Finset.exists_max_image` on `hfin.toFinset`.

### [`ESS.blowupLimitClauses_restrict_prod_eq`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/EscauriazaSereginSverak/Endpoint/BlowupLimitClausesModulusEstimate.lean#L34-L40) — `lean-pool-0878`

Snippet: `samples/lean-pool/lean-pool-0878.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.Measure.prod_restrict
- **file**: Mathlib/MeasureTheory/Measure/Prod.lean
- **derivation**: by
  unfold spaceTimeSet
  exact (Measure.prod_restrict C I).symm
- **proof_uses_it**: True
- **explanation**: Mathlib's `Measure.prod_restrict` says `(μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)`. Here `spaceTimeSet C I` is by definition `C ×ˢ I`, and `ParabolicPoint = Vec3 × ℝ`, so `volume` on it is `volume.prod volume` by `rfl`. The theorem is `prod_restrict` with μ = volume on Vec3, ν = volume on ℝ, s = C and t = I, and the sides swapped. The library's proof already does this: `rw [Measure.prod_restrict]; rfl`.

### [`measure_ball_pos_of_mem_support`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/FormalizingGMT/TangentMeasures/Basic.lean#L193-L196) — `lean-pool-0898`

Snippet: `samples/lean-pool/lean-pool-0898.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MeasureTheory.Measure.mem_support_iff_forall
- **file**: Mathlib/MeasureTheory/Measure/Support.lean
- **derivation**: (Measure.mem_support_iff_forall a).mp ha _ (ball_mem_nhds a hρ)
- **proof_uses_it**: True
- **explanation**: Mathlib has `Measure.mem_support_iff_forall`: x ∈ μ.support ↔ ∀ U ∈ 𝓝 x, 0 < μ U. The theorem is the case where U is the open ball `ball a ρ` in `EuclideanSpace ℝ (Fin n)`. The ball is a neighbourhood of `a` by `ball_mem_nhds`, which Mathlib already has. I found no Mathlib lemma that states this for balls directly. I searched Support.lean and grepped MeasureTheory for support/positivity lemmas.

### [`NavierStokes.FlatCovariance.determinant_columns`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/NavierStokes/TorusAverages.lean#L736-L739) — `lean-pool-0901`

Snippet: `samples/lean-pool/lean-pool-0901.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.det_mul_row
- **file**: Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean
- **derivation**: by simpa [columns, Fin.prod_univ_two] using Matrix.det_mul_row c G
- **explanation**: `columns G c i j = c j * G i j` (scaling column j by c j). Mathlib's `Matrix.det_mul_row v A` states `det (of fun i j => v j * A i j) = (∏ i, v i) * det A`. With n = Fin 2 and v = c, the product `∏ i, c i` becomes `c 0 * c 1` by `Fin.prod_univ_two`. The library proves it by direct `det_fin_two` expansion and `ring` instead. The `of` wrapper is defeq to the plain function, so `simpa` should handle it.

### [`PiMat.center`](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Monlib4/RepTheory/AutMat.lean#L581-L585) — `lean-pool-0979`

Snippet: `samples/lean-pool/lean-pool-0979.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.center_pi
- **file**: Mathlib/Algebra/Group/Center.lean
- **derivation**: by rw [PiMat, Set.center_pi]; ext x; simp
- **explanation**: Mathlib's `Set.center_pi` says `Set.center (Π i, A i) = Set.univ.pi fun i => Set.center (A i)` for any family of `Mul` types. `PiMat R ι n` is an abbreviation for `Π i, Matrix (n i) (n i) R`. Instantiating `A i := Matrix (n i) (n i) R` and unfolding `Set.pi univ` (`{x | ∀ i ∈ univ, x i ∈ _}`) gives the target. The library's own proof goes through its `Matrix.pi_center`, which itself starts with `Set.center_pi`. I found no Mathlib lemma with the exact `{x | ∀ i, x i ∈ center _}` form, and the derivation above is untested. The `rw [PiMat]` step may be unnecessary, since the abbreviation should unfold on its own.


## FLT (Anthropic) (118 flagged)

### [`P2MW.S_ModularCurve_XOneP_eq_zero_of_proj_eq_zero_of_qDivisible_normFreePart_points_twoChartModel_x1_mul.TorusGoodSol.pt_ext_of_isDominant`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_eq_zero_of_proj_eq_zero_of_qDivisible_normFreePart_points_twoChartModel_x1_mul.lean#L218-L222) — `flt-anthropic-0003`

Snippet: `samples/flt-anthropic/flt-anthropic-0003.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.ext_of_isDominant_of_isSeparated
- **file**: Mathlib/AlgebraicGeometry/Morphisms/Separated.lean
- **derivation**: haveI := hsep
Subtype.ext (ext_of_isDominant_of_isSeparated f (a.2.trans b.2.symm) ι h)
- **proof_uses_it**: True
- **explanation**: Mathlib's `ext_of_isDominant_of_isSeparated [IsReduced X] {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s) (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g` carries all the content. The theorem here is the case X := T, Y := X, Z := Spec R, s := f, applied to the underlying morphisms a.1 and b.1. Their compatibility with f comes from the structure proofs a.2 and b.2 (`a.2.trans b.2.symm`). `Subtype.ext` then turns equality of the underlying morphisms into equality of the `SchemeHomOver` elements. The library's current proof is exactly this derivation.

### [`P2MW.S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.AlgebraicCurve.WeierstrassCurve.Affine.algebraMap_polynomial_eq_mk_C`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean#L4792-L4794) — `flt-anthropic-0010`

Snippet: `samples/flt-anthropic/flt-anthropic-0010.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WeierstrassCurve.Affine.CoordinateRing.smul
- **file**: Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean
- **derivation**: by rw [Algebra.algebraMap_eq_smul_one, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
- **explanation**: Mathlib has `CoordinateRing.smul (x : R[X]) (y : W'.CoordinateRing) : x • y = mk W' (C x) * y`. Take y = 1. Then `algebraMap p = p • 1 = mk (C p) * 1 = mk (C p)`. Mathlib has no lemma that states the `algebraMap` form directly. I searched the EllipticCurve directory for `algebraMap` and `mk`. The library's proof is `rfl`, so it does not use the Mathlib lemma. I did not check the derivation's exact syntax, since I can't run Lean.

### [`P2MW.S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.ModularCurve.CuspDecayOfAux.qL_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isBigO_slash_realizeOf_mul_deriv_realizeOf_of_forall_ordDifferential_nonneg.lean#L116-L119) — `flt-anthropic-0016`

Snippet: `samples/flt-anthropic/flt-anthropic-0016.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModularForm.qExpansion_add
- **file**: Mathlib/NumberTheory/ModularForms/QExpansion.lean
- **derivation**: simp only [qL, ModularForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods Γ), PowerSeries.coe_add]
- **proof_uses_it**: True
- **explanation**: qL is a local abbrev for the Laurent-series coercion of `qExpansion 1 f`. The theorem is additivity of that expansion, which is exactly Mathlib's `ModularForm.qExpansion_add` at h = 1 (with `one_pos` and `one_mem_strictPeriods`). The current proof applies that lemma, then pushes the coercion through the sum with `PowerSeries.coe_add`. I did not look for a Mathlib `qL` or LaurentSeries-valued version. The match rests on `qL` unfolding to the coerced `qExpansion 1 f`, and I only skimmed `qL`'s definition and did not re-read it in full.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots.KcRsCellChoice.embS_mulSingle`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_unisolvence_refPoint_cutoff_of_linearIndependent_slots.lean#L328-L333) — `flt-anthropic-0019`

Snippet: `samples/flt-anthropic/flt-anthropic-0019.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidHom.noncommPiCoprod_mulSingle
- **file**: Mathlib/GroupTheory/NoncommPiCoprod.lean
- **derivation**: MonoidHom.noncommPiCoprod_mulSingle (fun q : ↥SQ => embAt (q : HeightOneSpectrum (𝓞 ℚ))) p x
- **proof_uses_it**: True
- **explanation**: embS SQ is defined as MonoidHom.noncommPiCoprod (fun p => embAt p) (commutation proof). The theorem is exactly Mathlib's `noncommPiCoprod_mulSingle` (noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y) with ϕ = embAt and the index type ↥SQ. The library's proof is a direct application of it after unfolding the definition.

### [`P2MW.S_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic.GaloisRep.MultHalfAux.postComp_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRep_exists_bialgEquiv_monoidAlgebra_of_finiteFlatHopf_of_galoisCyclotomic.lean#L89-L95) — `flt-anthropic-0022`

Snippet: `samples/flt-anthropic/flt-anthropic-0022.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgHom.cancel_left
- **file**: Mathlib/Algebra/Algebra/Hom.lean
- **derivation**: fun f g h => WithConv.ext ((AlgHom.cancel_left hψ).mp (congrArg WithConv.ofConv h))
- **explanation**: `postComp ψ f` is defined as `toConv (ψ.comp (ofConv f))`. So the theorem says that `f ↦ ψ.comp f` is injective on `H →ₐ[R] A` when `ψ` is injective, after unwrapping `WithConv`. `AlgHom.cancel_left` states that, for injective `f`, `f.comp g₁ = f.comp g₂ ↔ g₁ = g₂`. The theorem follows by unfolding `postComp` (definitional) and applying `WithConv.ext` (`ofConv_injective`). I did not find a Mathlib lemma about `postComp` itself; the only Mathlib `postComp` declarations are in category theory and Dold–Kan. The current proof is a direct `AlgHom.ext` argument and does not use `cancel_left`.

### [`P2MW.S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst.VbUnrq.eval_map_coe`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_ramificationIndexAlong_heckeAlphaBar_eq_one_and_eq_of_isChartAt_of_isStrictFst.lean#L290-L293) — `flt-anthropic-0055`

Snippet: `samples/flt-anthropic/flt-anthropic-0055.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.eval_map_apply
- **file**: Mathlib/Algebra/Polynomial/Eval/Defs.lean
- **derivation**: exact (Polynomial.eval_map_apply W.toValuationSubring.subtype x).symm
- **explanation**: Mathlib's `Polynomial.eval_map_apply (f : R →+* S) (x : R) : (p.map f).eval (f x) = f (p.eval x)`. Taking f to be `W.toValuationSubring.subtype : W.toValuationSubring →+* F'`, whose application to x is defeq to the coercion `(x : F')`, gives the target (after `.symm`). The current proof instead uses `eval_map` and `eval₂_hom`, which are the ingredients of `eval_map_apply` itself.

### [`P2MW.S_Padic_index_range_powMonoidHom_units_of_ne_two.Ws26U4.natCast_prime_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Padic_index_range_powMonoidHom_units_of_ne_two.lean#L87-L87) — `flt-anthropic-0056`

Snippet: `samples/flt-anthropic/flt-anthropic-0056.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.cast_ne_zero
- **file**: Mathlib/Algebra/CharZero/Defs.lean
- **derivation**: Nat.cast_ne_zero.mpr hp.out.ne_zero
- **proof_uses_it**: True
- **explanation**: The theorem says (p : ℚ_[p]) ≠ 0 for p prime. Mathlib's `Nat.cast_ne_zero : (n : R) ≠ 0 ↔ n ≠ 0` holds in any `AddMonoidWithOne` with `CharZero`. Taking R = ℚ_[p] and n = p gives it, with p ≠ 0 coming from primality. I found no Padic-specific lemma with this statement.

### [`P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.W1xLA.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_AuxLevel_exists_isLevelAutAt_of_mem_gamma0.lean#L610-L612) — `flt-anthropic-0060`

Snippet: `samples/flt-anthropic/flt-anthropic-0060.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HahnSeries.C_eq_algebraMap
- **file**: Mathlib/RingTheory/HahnSeries/Multiplication.lean
- **derivation**: exact congrFun (HahnSeries.C_eq_algebraMap (R := L) (Γ := ℤ)) c
- **explanation**: Mathlib's `HahnSeries.C_eq_algebraMap : C = algebraMap R R⟦Γ⟧` (proved by `rfl`) is the same statement as the target, stated as an equality of ring homs. The target is its pointwise form at `c`, with Γ := ℤ and R := L (`LaurentSeries L` is `HahnSeries ℤ L`). The library's proof rewrites with a local lemma `algebraMap_laurentSeries_eq_single`, which I could not find in Mathlib, instead of using this declaration.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq.WGenH.inseparable_genericPoint`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_algEquiv_pointEquivPlace_eq_ofAlgAut_smul_of_comp_w_eq.lean#L24-L25) — `flt-anthropic-0080`

Snippet: `samples/flt-anthropic/flt-anthropic-0080.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.genericPoint_eq_of_isOpenImmersion
- **file**: Mathlib/AlgebraicGeometry/FunctionField.lean
- **derivation**: by rw [genericPoint_eq_of_isOpenImmersion ψ]
- **proof_uses_it**: True
- **explanation**: The theorem says the generic point of Mdl.C is inseparable from its image under ψ. Mathlib's `genericPoint_eq_of_isOpenImmersion` (f : X ⟶ Y, [IsOpenImmersion f], irreducible spaces) gives `f (genericPoint X) = genericPoint Y`. Take f = ψ, which is an open immersion because it is an iso, and X = Y = Mdl.C, which is irreducible because `IsIntegral C` is a field of `CurveModel`. After the rewrite the goal is `Inseparable g g`, which `rw` closes with `rfl` via `Inseparable.refl`. The library's own proof goes through a local wrapper `base_genericPoint`, whose body is exactly this Mathlib lemma applied to ψ. I found no Mathlib lemma stating `Inseparable` for generic points directly, so this is a special case rather than a duplicate.

### [`P2MW.S_CuspForm_petersson_self_eq_zero_iff.AlliAux1Pet.tr_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_petersson_self_eq_zero_iff.lean#L20-L21) — `flt-anthropic-0084`

Snippet: `samples/flt-anthropic/flt-anthropic-0084.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SlashAction.slash_one
- **file**: Mathlib/NumberTheory/ModularForms/SlashActions.lean
- **derivation**: by rw [tr, inv_one, SlashAction.slash_one]
- **proof_uses_it**: True
- **explanation**: `tr f 1` unfolds to `⇑f ∣[k] (1⁻¹ : SL(2, ℤ))`. After `inv_one` this is `⇑f ∣[k] 1`, which `SlashAction.slash_one` (a structure field, tagged `@[simp]`) rewrites to `⇑f`. The current proof, `simp [tr]`, uses that simp lemma. So the theorem is Mathlib's `slash_one` with the library's `tr` definition unfolded.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le.SVDGlue.continuous_det`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_forall_setIntegral_localLevelOne_rowSlice_whittaker_shell_eq_zero_of_le.lean#L109-L115) — `flt-anthropic-0086`

Snippet: `samples/flt-anthropic/flt-anthropic-0086.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.continuous_det
- **file**: Mathlib/Topology/Algebra/Group/Matrix.lean
- **derivation**: exact Matrix.GeneralLinearGroup.continuous_det
- **explanation**: Mathlib's `Matrix.GeneralLinearGroup.continuous_det` states `Continuous (det : GL n R → Rˣ)` for a commutative topological ring `R` with `Fintype n` and `DecidableEq n`. The theorem states the same thing for `n = Fin 2` and `R = HeightOneSpectrum.adicCompletion ℚ p`. This is a topological ring, since it is a valued field. Mathlib's proof is essentially the same as the library's: `Units.continuous_iff` plus continuity of the determinant of matrices.

### [`P2MW.S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.K45VolB3.iterate_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_finset_forall_eq_mul_algebraMap_mul_of_sigmaTensor_eq_mul.lean#L218-L220) — `flt-anthropic-0093`

Snippet: `samples/flt-anthropic/flt-anthropic-0093.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: iterate_map_mul
- **file**: Mathlib/Algebra/Group/Hom/Defs.lean
- **derivation**: exact iterate_map_mul σE i x y
- **explanation**: `sigmaTensor K L A σ` is defined as a ring homomorphism `L ⊗[K] A →+* L ⊗[K] A`. Mathlib's `iterate_map_mul` states `f^[n] (x * y) = f^[n] x * f^[n] y` for any `f` with `[MulHomClass F M M]`. Taking `f := σE` and `n := i` gives the theorem. The current proof instead rewrites with the library's own `sigmaTensor_pow` and then applies `map_mul`. I read the Mathlib statement but did not check that the `MulHomClass` instance resolves for `RingHom`, which I expect it does.

### [`P2MW.S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.R4GC.qC_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem.lean#L1440-L1442) — `flt-anthropic-0104`

Snippet: `samples/flt-anthropic/flt-anthropic-0104.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModularForm.qExpansion_eq_zero_iff
- **file**: Mathlib/NumberTheory/ModularForms/QExpansion.lean
- **derivation**: rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods f]
exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective
- **proof_uses_it**: True
- **explanation**: qC f is defined as the image of qExpansion 1 f under the embedding ofPowerSeries ℤ ℂ into LaurentSeries ℂ. Mathlib's ModularForm.qExpansion_eq_zero_iff (h = 1, Γ = Γ m M') says qExpansion 1 f = 0 ↔ f = 0. The theorem is that statement with the power-series side pushed into Laurent series, using injectivity of the embedding (HahnSeries.ofPowerSeries_injective). The derivation is the library's current two-line proof. It is a borderline case: qC is the library's own definition, and the proof also needs the injectivity lemma. I found no Mathlib lemma about qC itself.

### [`P2MW.S_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_two.ModularCurve.KSharpPinQ2.laurentBaseChange_mono`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_mem_iff_mem_igusaGaussRing_of_coe_eq_qExpand_of_forall_mem_integers_mem_of_eq_two.lean#L118-L120) — `flt-anthropic-0106`

Snippet: `samples/flt-anthropic/flt-anthropic-0106.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IntermediateField.adjoin.mono
- **file**: Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean
- **derivation**: IntermediateField.adjoin.mono L _ _ (Set.image_mono h)
- **proof_uses_it**: True
- **explanation**: laurentBaseChange L F is defined as IntermediateField.adjoin L (coeffEmb L '' (F : Set (LaurentSeries ℚ))). The theorem says this is monotone in F. This is IntermediateField.adjoin.mono (S ⊆ T → adjoin F S ≤ adjoin F T), instantiated at the two image sets. The hypothesis comes from Set.image_mono h. The library's proof is exactly this one-liner. The only library-specific part is unfolding the definition. I did not search further for a separate monotonicity lemma for this definition, since it is the library's own.

### [`P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero.WeierstrassCurve.M5HD2.psCoeff_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero.lean#L313-L315) — `flt-anthropic-0107`

Snippet: `samples/flt-anthropic/flt-anthropic-0107.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: PowerSeries.coeff_coeToMvPowerSeries
- **file**: Mathlib/RingTheory/PowerSeries/Basic.lean
- **derivation**: (PowerSeries.coeff_coeToMvPowerSeries n).symm
- **explanation**: Mathlib's `PowerSeries.coeff_coeToMvPowerSeries` states `MvPowerSeries.coeff (Finsupp.single () n) f = f.coeff n`, proved by `rfl`. The target is the same equation with the two sides swapped. The target's `CommRing` assumption is stronger than the `Semiring` that Mathlib needs. The target's own proof uses `PowerSeries.coeff_def`, a different declaration.

### [`P2MW.S_WeierstrassCurve_exists_prePsi_eq_expand.WeierstrassCurve.Universal.Ψ₂Sq_𝓦p_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_exists_prePsi_eq_expand.lean#L273-L277) — `flt-anthropic-0125`

Snippet: `samples/flt-anthropic/flt-anthropic-0125.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WeierstrassCurve.Ψ₂Sq_ne_zero
- **file**: Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Degree.lean
- **derivation**: exact (𝓦p p).Ψ₂Sq_ne_zero (four_ne_zero_Rp p hp2)
- **explanation**: Mathlib's `WeierstrassCurve.Ψ₂Sq_ne_zero (W : WeierstrassCurve R) (h : (4 : R) ≠ 0) : W.Ψ₂Sq ≠ 0` holds for any commutative ring R. Taking R = Rp p, W = 𝓦p p, and h = the library's `four_ne_zero_Rp p hp2` gives the theorem. The library proves it by extracting coefficient 3 by hand, which is essentially Mathlib's `coeff_Ψ₂Sq`.

### [`P2MW.S_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_circleIndexDrop.AnnulusG1.le_map_sum_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_circleIndexDrop.lean#L266-L277) — `flt-anthropic-0140`

Snippet: `samples/flt-anthropic/flt-anthropic-0140.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddValuation.map_le_sum
- **file**: Mathlib/RingTheory/Valuation/Basic.lean
- **derivation**: exact tsub_le_iff_right.mp (v.map_le_sum (g := n - w) fun k hk => tsub_le_iff_right.mpr (h k hk))
- **explanation**: AddValuation.map_le_sum says that if g ≤ v (f i) for all i ∈ s, then g ≤ v (∑ i ∈ s, f i). It holds for any LinearOrderedAddCommMonoidWithTop value type, and ℕ∞ is one. Take g = n - w, using truncated subtraction in ℕ∞. Then n ≤ v (a k) + w is equivalent to n - w ≤ v (a k), by tsub_le_iff_right (ℕ∞ has OrderedSub). Applying that equivalence in both directions gives the target. The library instead proves it by induction on the finset. I did not check that the one-line derivation compiles.

### [`P2MW.S_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback.FunFamilySpread.appLE_appLE_of_comp_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback.lean#L48-L52) — `flt-anthropic-0153`

Snippet: `samples/flt-anthropic/flt-anthropic-0153.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE
- **file**: Mathlib/AlgebraicGeometry/Scheme.lean
- **derivation**: subst hc
rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]
- **proof_uses_it**: True
- **explanation**: Mathlib's `Scheme.Hom.appLE_comp_appLE (f : X ⟶ Y) (g : Y ⟶ Z) U V W e₁ e₂ : g.appLE U V e₁ ≫ f.appLE V W e₂ = (f ≫ g).appLE U W _` is the categorical form of the target. The target applies both sides to z and substitutes d = c ≫ s. The proof-irrelevant ≤ argument on the right-hand side matches by proof irrelevance. I found no elementwise (`_apply`) version in Mathlib. The current proof is `subst` plus `comp_apply` plus this lemma, which is routine glue around it.

### [`P2MW.S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.AlgebraicCurve.AlgebraicCurve.adeleBddPrincipal_eq_comap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_stichtenothGenusExists_of_ratFunc_tower.lean#L791-L793) — `flt-anthropic-0183`

Snippet: `samples/flt-anthropic/flt-anthropic-0183.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.comap_sup_of_injective
- **file**: Mathlib/LinearAlgebra/Span/Basic.lean
- **derivation**: (Submodule.comap_sup_of_injective (adeleSpace K F).subtype_injective (by simpa using adeleBdd_le_adeleSpace) (by simpa using globalSub_le_adeleSpace)).symm
- **explanation**: `adeleBddPrincipal` is an abbrev for `(adeleBdd D).comap C.subtype ⊔ (globalSub K F).comap C.subtype` with `C = adeleSpace K F`. The theorem says this equals `(adeleBdd D ⊔ globalSub K F).comap C.subtype`. Mathlib's `Submodule.comap_sup_of_injective` states `comap f (p ⊔ q) = comap f p ⊔ comap f q` for injective `f` when `p` and `q` lie in `range f`. Taking `f := C.subtype` gives the theorem. The side goals `p ≤ range C.subtype` reduce to `p ≤ C` by `Submodule.range_subtype`, which `simp` knows. The current proof instead uses a local helper, `Submodule.comap_subtype_sup_of_le_of_le`, defined in the same file, and that helper is itself a special case of the Mathlib lemma.

### [`P2MW.S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete.TQStruct.isNoetherianRing_of_finite`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_TWLevel_HeckeRing_finite_and_isLocalRing_and_isAdicComplete.lean#L74-L77) — `flt-anthropic-0194`

Snippet: `samples/flt-anthropic/flt-anthropic-0194.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: IsNoetherianRing.of_finite
- **file**: Mathlib/RingTheory/Noetherian/Basic.lean
- **derivation**: IsNoetherianRing.of_finite 𝒪 A
- **explanation**: Mathlib's `IsNoetherianRing.of_finite (R S) [Ring R] [Ring S] [Module R S] [IsScalarTower R S S] [IsNoetherianRing R] [Module.Finite R S] : IsNoetherianRing S` is the same statement. The theorem's setting has `Algebra 𝒪 A`, which gives the `Module` instance and the `IsScalarTower 𝒪 A A` instance. Mathlib's proof is `isNoetherian_of_tower R inferInstance`, which is the same as the library's proof.

### [`P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal.EllGermBridge.two_ne_zero_adicCompletion`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal.lean#L944-L948) — `flt-anthropic-0196`

Snippet: `samples/flt-anthropic/flt-anthropic-0196.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.charZero_of_charZero
- **file**: Mathlib/Algebra/Algebra/Basic.lean
- **derivation**: haveI : CharZero (v.adicCompletion K) := Algebra.charZero_of_charZero K _
exact two_ne_zero
- **explanation**: The theorem says 2 ≠ 0 in the adic completion of a number field. Mathlib has `Algebra.charZero_of_charZero`, which says an algebra A over a char-zero ring R (with faithful smul) is char zero. Take R = K and A = v.adicCompletion K, using the existing `Algebra K (v.adicCompletion K)` instance and `CharZero K` from `NumberField`. Then `two_ne_zero` applies, since a char-zero semiring has `NeZero (2 : _)`. The library's own proof instead shows injectivity of algebraMap by hand. I found no ready-made `CharZero` instance for `adicCompletion`. I did not check the explicit/implicit argument order of `Algebra.charZero_of_charZero`, so the derivation may need `(R := K) (A := _)`.

### [`P2MW.S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash.TraceDepletion.denom_SL_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_HasNebentypus_qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash.lean#L429-L432) — `flt-anthropic-0209`

Snippet: `samples/flt-anthropic/flt-anthropic-0209.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: UpperHalfPlane.denom_ne_zero
- **file**: Mathlib/Analysis/Complex/UpperHalfPlane/MoebiusAction.lean
- **derivation**: rw [← ModularGroup.denom_apply]; exact UpperHalfPlane.denom_ne_zero _ τ
- **proof_uses_it**: True
- **explanation**: The target says that the lower row of an SL(2,ℤ) matrix evaluated at τ, c·τ + d, is nonzero. Mathlib's `UpperHalfPlane.denom_ne_zero (g : GL (Fin 2) ℝ) (z : ℍ) : denom g z ≠ 0` states this for GL(2,ℝ), and the target follows by taking g to be the image of γ. `ModularGroup.denom_apply` (`denom g z = g 1 0 * z + g 1 1 := rfl`, same file) rewrites `denom γ τ` into the explicit expression. The library's current proof is exactly this two-line derivation. I found no single Mathlib lemma that states the explicit integer-cast form directly, so this is a special case and not a duplicate.

### [`P2MW.S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.EtaleCoordK1a.rankAtStalk_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_exists_isStandardEtale_mvPolynomial_localizationAway_of_smooth_of_kaehlerDifferential.lean#L13-L24) — `flt-anthropic-0236`

Snippet: `samples/flt-anthropic/flt-anthropic-0236.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.finrank_fiber_eq_finrank
- **file**: Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean
- **derivation**: rw [Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank]
exact Module.finrank_eq_of_rank_eq hrank
- **explanation**: Mathlib's `Module.rankAtStalk_eq` gives `rankAtStalk M p = finrank κ(p) (p.asIdeal.Fiber M)`. For a domain, `Ideal.finrank_fiber_eq_finrank` says that equals `finrank R M` (flat and finite hypotheses are in scope; finite follows from finite presentation). The theorem's `rank = n` hypothesis then converts to `finrank R M = n` via `Module.finrank_eq_of_rank_eq`. The library's proof instead goes through localization at the zero ideal and uses local constancy of the rank. I only read the statements, since I can't run Lean. I did not check the `Module.Finite` instance on `M` or that `p.asIdeal.IsPrime` is found by instance search.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.DualB.inv_ofReal_cpow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.lean#L233-L235) — `flt-anthropic-0243`

Snippet: `samples/flt-anthropic/flt-anthropic-0243.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Complex.inv_cpow_ofReal_nonneg
- **file**: Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean
- **derivation**: by rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hr.le, Complex.cpow_neg]
- **explanation**: Mathlib has `inv_cpow_ofReal_nonneg : 0 ≤ a → ((a:ℂ)⁻¹) ^ r = ((a:ℂ) ^ r)⁻¹`. The theorem is this lemma after two rewrites. First rewrite `((r⁻¹:ℝ):ℂ)` to `(r:ℂ)⁻¹` with `ofReal_inv`. Then rewrite `(↑r ^ s)⁻¹` to `↑r ^ (-s)` with `cpow_neg`. The current proof does the same thing but uses the more general `Complex.inv_cpow` and proves the arg side condition by hand. `inv_cpow_ofReal_nonneg` already packages that side condition.

### [`P2MW.S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero.SmoothPointDVR.primeCompl_le_nonZeroDivisors`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Place_existsUnique_sub_algebraMap_mem_nonunits_of_eval_pderiv_ne_zero.lean#L183-L187) — `flt-anthropic-0264`

Snippet: `samples/flt-anthropic/flt-anthropic-0264.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.primeCompl_le_nonZeroDivisors
- **file**: Mathlib/RingTheory/Ideal/Operations.lean
- **derivation**: Ideal.primeCompl_le_nonZeroDivisors (𝔮 hker hab)
- **explanation**: Mathlib has `theorem Ideal.primeCompl_le_nonZeroDivisors {R} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.primeCompl ≤ nonZeroDivisors R`. The target is this statement with R := A K x y and P := 𝔮 hker hab. A K x y is a subalgebra of the field F, so it has no zero divisors by the existing Subalgebra instances. The `[P.IsPrime]` instance is the scoped `𝔮_isPrime`, which is in scope. The library's own proof re-proves the lemma by hand instead of using this declaration.

### [`P2MW.S_GaloisRepAdic_ordinaryCondition_of_isEquiv.GaloisRepAdic.LCSol.det_apply_baseChangeAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRepAdic_ordinaryCondition_of_isEquiv.lean#L92-L97) — `flt-anthropic-0265`

Snippet: `samples/flt-anthropic/flt-anthropic-0265.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.det_baseChange
- **file**: Mathlib/LinearAlgebra/Charpoly/BaseChange.lean
- **derivation**: letI : Algebra A B := φ.toAlgebra
exact LinearMap.det_baseChange (ρ.ρ σ)
- **proof_uses_it**: True
- **explanation**: Mathlib's `LinearMap.det_baseChange` states `det (f.baseChange A) = algebraMap R A (det f)`. The theorem is this lemma with `R := A`, `A := B` and the algebra structure `φ.toAlgebra`, applied to `f := ρ.ρ σ`. The library's `baseChangeAlong` is defeq to `LinearMap.baseChange`, so unfolding it closes the goal. I did not open the definition of `baseChangeAlong` in the flt-anthropic library. The proof's `show` step relies on that defeq, and the existing proof already applies the lemma.

### [`P2MW.S_Function_orbitCensus_of_dihedralThree_relations.P2MKcOrbitCensus.b_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Function_orbitCensus_of_dihedralThree_relations.lean#L14-L17) — `flt-anthropic-0268`

Snippet: `samples/flt-anthropic/flt-anthropic-0268.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Function.LeftInverse.injective
- **file**: Init/Data/Function.lean
- **derivation**: Function.LeftInverse.injective (g := fun x => b (b x)) hb
- **explanation**: The hypothesis hb says b ∘ b ∘ b = id pointwise. That is exactly `Function.LeftInverse (fun x => b (b x)) b`, up to beta reduction. `Function.LeftInverse.injective : LeftInverse g f → Injective f` (Lean core, Init/Data/Function.lean:91) then gives `Injective b`. The library's proof reaches the same conclusion with a manual `congrArg` and `simpa`. I did not run Lean, so the explicit `g :=` argument is there to help unification.

### [`P2MW.S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.UqNSol.fstDiv_sum`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_isGoodDiv_heckeDivBar_self_and_glueData_mem_admissible.lean#L358-L366) — `flt-anthropic-0271`

Snippet: `samples/flt-anthropic/flt-anthropic-0271.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finsupp.filter_sum
- **file**: Mathlib/Data/Finsupp/Basic.lean
- **derivation**: by classical
  unfold PlaceSpecialization.fstDiv
  exact Finsupp.filter_sum _ _
- **explanation**: PlaceSpecialization.fstDiv D is defined as D.filter P.IsStrictFst, where a Divisor is a Finsupp from places to ℤ. The theorem says that filtering distributes over a Finset sum. That is Finsupp.filter_sum, stated as (∑ a ∈ s, f a).filter p = ∑ a ∈ s, filter p (f a). Instantiate it with p := P.IsStrictFst after unfolding fstDiv. The current proof instead does induction using fstDiv_add and Finsupp.filter_zero. I did not check that Divisor unfolds to a Finsupp (I assumed it), so `exact` might need a `show` or `change` first. I did not run the derivation.

### [`groupCohomology.comap_fixingSubgroup_eq_ker`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_GroupCohomology_LevelSubgroup.lean#L9-L14) — `flt-anthropic-0288`

Snippet: `samples/flt-anthropic/flt-anthropic-0288.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IntermediateField.restrictNormalHom_ker
- **file**: Mathlib/FieldTheory/Galois/Basic.lean
- **derivation**: rw [← IntermediateField.restrictNormalHom_ker F, MonoidHom.comap_ker]; rfl
- **proof_uses_it**: True
- **explanation**: Mathlib has `IntermediateField.restrictNormalHom_ker (E) [Normal K E] : (restrictNormalHom E).ker = E.fixingSubgroup`. The target is the same statement pulled back along the homomorphism `r`. The pullback step is the generic lemma `MonoidHom.comap_ker`, which turns `(restrictNormalHom F).ker.comap r` into `((restrictNormalHom F).comp r).ker`. It is ordinary group-theory glue, not Galois content. The library's proof does exactly this, with the Mathlib lemma instantiated at `ℚ` and `AlgebraicClosure ℚ`. I found no single Mathlib lemma that states the comap form directly.

### [`P2MW.S_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq.CSTowerT21.Stab.not_mem_of_prime_ne`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_CosetGraph_awayUnits_meetOrder_eq_inf_map_conj_of_finiteAdeleEvalAt_eq.lean#L231-L237) — `flt-anthropic-0290`

Snippet: `samples/flt-anthropic/flt-anthropic-0290.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.IsPrime.notMem_of_isCoprime_of_mem
- **file**: Mathlib/RingTheory/Ideal/Operations.lean
- **derivation**: exact Ideal.IsPrime.notMem_of_isCoprime_of_mem (I := v.asIdeal) (Nat.Coprime.cast ((Nat.coprime_primes hp hℓ).2 hne.symm)) hv
- **explanation**: The theorem says that two distinct natural primes p and ℓ cannot both lie in a height-one prime ideal v.asIdeal of 𝓞 ℚ. Mathlib's `Ideal.IsPrime.notMem_of_isCoprime_of_mem` says that if x and y are coprime and x ∈ I for a prime ideal I, then y ∉ I. Take I = v.asIdeal, which is prime as a HeightOneSpectrum ideal, and x = (p : 𝓞 ℚ), y = (ℓ : 𝓞 ℚ). Coprimality of the casts comes from `Nat.Coprime.cast` (Mathlib/RingTheory/Coprime/Lemmas.lean) applied to `Nat.coprime_primes`. The library's own proof goes through `natGenerator` instead and does not use this lemma. I did not find a Mathlib lemma that states the result directly for HeightOneSpectrum and natural primes. I searched for `natGenerator`, for prime-ideal membership lemmas, and for coprimality lemmas.

### [`P2MW.S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.X1BoundedDenominators.disc_smul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_isIntegralQExp_smul_of_ratCast_qExpansion.lean#L189-L194) — `flt-anthropic-0303`

Snippet: `samples/flt-anthropic/flt-anthropic-0303.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SlashInvariantForm.slash_action_eqn''
- **file**: Mathlib/NumberTheory/ModularForms/SlashInvariantForms.lean
- **derivation**: by simpa [CuspForm.coe_discriminant, -ModularGroup.sl_moeb] using SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant (Γ := 𝒮ℒ) (γ := (α : GL (Fin 2) ℝ)) ⟨α, rfl⟩ τ
- **proof_uses_it**: True
- **explanation**: Mathlib has no lemma stating the transformation law of `Δ` under SL(2,ℤ) directly. Mathlib's `Discriminant.lean` only has `discriminant_T_invariant` and `discriminant_S_invariant`. The general law for slash-invariant forms is `SlashInvariantForm.slash_action_eqn''`: `f (γ • z) = denom γ z ^ k * f z` for `γ ∈ Γ`. Taking `f := CuspForm.discriminant : CuspForm 𝒮ℒ 12`, `Γ := 𝒮ℒ` and `γ := (α : GL (Fin 2) ℝ)` gives the theorem. `CuspForm.coe_discriminant` is `rfl`, and `ModularGroup.sl_moeb` is `rfl` and only converts `α • τ` between the SL and GL actions. The library's proof is exactly this instantiation plus that glue, so the theorem has no independent content beyond `slash_action_eqn''`. `SlashInvariantForm.slash_action_eqn_SL''` is a variant of the same lemma for a subgroup of SL(2,ℤ).

### [`P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.ModularCurve.ComplexPlaceDictionaryOf.RamEqCard.two_mul_card_div_two`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_ComplexPlaceDictionaryOf_two_mul_ramification_eq_card_stabilizer.lean#L857-L863) — `flt-anthropic-0306`

Snippet: `samples/flt-anthropic/flt-anthropic-0306.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.mul_div_cancel'
- **file**: Init/Data/Nat/Dvd.lean
- **derivation**: exact_mod_cast Nat.mul_div_cancel' (two_dvd_card_stabilizer σ)
- **explanation**: The statement is the ℤ-cast form of `2 * (n / 2) = n` for n = Nat.card (stabilizer SL(2,ℤ) σ), given 2 ∣ n. The library lemma `two_dvd_card_stabilizer` supplies 2 ∣ n. Lean core's `Nat.mul_div_cancel' : n ∣ m → n * (m / n) = m` gives the rest with n := 2. Casting to ℤ is routine glue (`exact_mod_cast`). The current proof uses `Nat.mul_div_cancel_left` with `push_cast; ring` instead.

### [`P2MW.S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight.Ws31.C3Glue.L5_deriv_congr`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_forall_lintegral_norm_deriv_axis_continuation_weylIntertwiningIntegral_le_mul_pow_archParam_weight.lean#L274-L276) — `flt-anthropic-0307`

Snippet: `samples/flt-anthropic/flt-anthropic-0307.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.EqOn.deriv
- **file**: Mathlib/Analysis/Calculus/Deriv/Basic.lean
- **derivation**: Set.EqOn.deriv h hU hs₀
- **explanation**: Mathlib's `Set.EqOn.deriv` has hypotheses `hfg : s.EqOn f g` and `hs : IsOpen s`. It concludes `s.EqOn (deriv f) (deriv g)`. Applying that to `hs₀ : s₀ ∈ U` gives `deriv F s₀ = deriv G s₀`. The hypothesis `h : ∀ s ∈ U, F s = G s` is definitionally `Set.EqOn F G U`. The statement is the general one with the field 𝕜 taken to be ℂ. The library's current proof goes through `Filter.EventuallyEq.deriv_eq` instead.

### [`P2MW.S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero.UnitTensorDescent.baseChange_cancelBaseChange`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TensorProduct_mem_span_unitTmul_of_forall_apply_eq_zero.lean#L118-L133) — `flt-anthropic-0311`

Snippet: `samples/flt-anthropic/flt-anthropic-0311.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
- **file**: Mathlib/LinearAlgebra/TensorProduct/Tower.lean
- **derivation**: LinearMap.congr_fun (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange R (FractionRing R) K K T T h) u
-- (if not closed by defeq: `by simpa [LinearMap.baseChange_eq_ltensor] using LinearMap.congr_fun (...) u`)
- **explanation**: Mathlib's lemma says lTensor f ∘ cancelBaseChange R A B M N = cancelBaseChange R A B M Q ∘ lTensor (lTensor f) as B-linear maps. Take A = FractionRing R, B = M = K, N = Q = T, f = h, and apply both sides to u. The left side is h.baseChange K, which is `lTensor K h` by `baseChange_eq_ltensor` or by definition. On the right, the inner map lTensor A A h is h.baseChange (FractionRing R), and the outer one is LinearMap.lTensor K of it (`coe_lTensor`). So the target is the pointwise form of the Mathlib lemma. The current proof is a manual induction and does not use it. I could not run Lean, so the final `simpa` or defeq step is unchecked.

### [`P2MW.S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor.ALLiP.map_int_mul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_IsEigenformWith_exists_changeLevel_and_qCoeff_sq_eq_or_exists_isEigenformWith_of_dvd_of_not_sq_dvd_of_not_dvd_conductor.lean#L41-L43) — `flt-anthropic-0314`

Snippet: `samples/flt-anthropic/flt-anthropic-0314.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Matrix.map_mul
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: Matrix.map_mul
- **explanation**: Matrix.map_mul states (L * M).map f = L.map f * M.map f for any non-unital ring-hom-class f. The target is this with f = algebraMap ℤ ℝ, a ring hom, so it is an instance of Matrix.map_mul with the same shape. The library's proof goes through RingHom.mapMatrix and map_mul instead.

### [`P2MW.S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic.P2mSemilin.inv_comp_base`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_Pic0_exists_semilinear_hom_of_pushforwardAlong_frobenius_of_representsRelSubPic.lean#L102-L105) — `flt-anthropic-0319`

Snippet: `samples/flt-anthropic/flt-anthropic-0319.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Iso.inv_comp_eq
- **file**: Mathlib/CategoryTheory/Iso.lean
- **derivation**: B.inv_comp_eq.mpr (by simpa only [Category.assoc] using hB.symm)
- **proof_uses_it**: True
- **explanation**: The theorem says that if B.hom ≫ c ≫ e = c for an isomorphism B : C ≅ C, then B.inv ≫ c = c ≫ e. This is `Iso.inv_comp_eq` (α.inv ≫ f = g ↔ f = α.hom ≫ g) with f := c and g := c ≫ e. The remaining side goal is hB.symm, with the associativity of composition rewritten by `Category.assoc`. The library's current proof is exactly this derivation. I did not look for a more direct Mathlib lemma.

### [`P2MW.S_ModularCurve_nonempty_ssPlaces_fibre.SsfrobNE.ModularCurve.jLineEquivOneC_commutes`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_nonempty_ssPlaces_fibre.lean#L50-L52) — `flt-anthropic-0327`

Snippet: `samples/flt-anthropic/flt-anthropic-0327.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: AlgEquiv.commutes
- **file**: Mathlib/Algebra/Algebra/Equiv.lean
- **derivation**: e.commutes c
- **proof_uses_it**: True
- **explanation**: jLineEquivOneC K N is a K-algebra equivalence (≃ₐ[K]). The theorem says its underlying ring equiv fixes algebraMap K _ c. That is AlgEquiv.commutes: e (algebraMap R A₁ r) = algebraMap R A₂ r. The only difference is the toRingEquiv coercion, which is defeq. The current proof is exactly `(jLineEquivOneC K N).commutes c`.

### [`P2MW.S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.RATIOCOVER.exists_eq_smul_of_mem_center`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_mem_ratio_eq_or_eq_inv_and_ratio_ne_of_ne_of_classReps.lean#L71-L74) — `flt-anthropic-0345`

Snippet: `samples/flt-anthropic/flt-anthropic-0345.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Basic.lean
- **derivation**: obtain ⟨a, ha⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
exact ⟨a, by rw [← ha, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
- **proof_uses_it**: True
- **explanation**: Mathlib states that g ∈ center (GL n R) ↔ g.val ∈ Set.range (Matrix.scalar n), for a commutative ring R and any finite n. Taking n = Fin 2 and R = K (a field) gives c = scalar a for some a. The target only has to rewrite `scalar a` as `a • 1`, using `scalar_apply` and `smul_one_eq_diagonal`. I found no Mathlib lemma that states the `a • 1` form directly, so the derivation is the library's own two-line proof.

### [`P2MW.S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top.AlgebraicCurve.PeriodLatticeIsLatticeProof.linearIndependent_of_card_le_of_span_eq_top`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top.lean#L39-L47) — `flt-anthropic-0347`

Snippet: `samples/flt-anthropic/flt-anthropic-0347.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: linearIndependent_of_top_le_span_of_card_le_finrank
- **file**: Mathlib/LinearAlgebra/Dimension/OrzechProperty.lean
- **derivation**: linearIndependent_of_top_le_span_of_card_le_finrank (by simp [hspan]) (by simpa using hcard)
- **proof_uses_it**: True
- **explanation**: Mathlib's theorem says that a finite family b : ι → M with ⊤ ≤ span R (range b) and Fintype.card ι ≤ finrank R M is linearly independent. The target is the case R = ℝ, ι = ↥(s : Set E) and b = Subtype.val for a Finset s. There range b = ↑s (Subtype.range_coe), so the span hypothesis is hspan. Fintype.card ↥↑s = s.card (Fintype.card_coe), so the card hypothesis is hcard. The current proof already applies this declaration, and the glue is only the two side goals (the span and card hypotheses), each closed by simp or simpa.

### [`P2MW.S_ModularCurve_transcendental_coeffEmb_jq.DivUSol.isScalarTower_rat`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_transcendental_coeffEmb_jq.lean#L128-L132) — `flt-anthropic-0368`

Snippet: `samples/flt-anthropic/flt-anthropic-0368.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsScalarTower.rat
- **file**: Mathlib/Algebra/Module/Rat.lean
- **derivation**: IsScalarTower.rat
- **explanation**: Mathlib has the instance `IsScalarTower.rat {R M} [Ring R] [AddCommGroup M] [Module R M] [Module ℚ R] [Module ℚ M] : IsScalarTower ℚ R M`. Taking R = AlgebraicClosure ℚ and M = LaurentSeries (AlgebraicClosure ℚ) gives the theorem. The scalar actions in the statement are `Algebra.toSMul`, which are the smul fields of the `Algebra` instances, so the `Module ℚ _` arguments are filled by the algebra structures. The theorem's `@` form with explicit instances is there to pin down the instances. The current proof does not use `IsScalarTower.rat`. It uses `IsScalarTower.of_algebraMap_eq` together with subsingleton-ness of `ℚ`-algebra maps. I did not check that the instance arguments unify, so the derivation is untested.

### [`P2MW.S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul.P2mKcZp2Matrix.linearIndependent_one_ω`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WittVector_exists_ringHom_matrix_padicInt_mul_eq_frobenius_mul_and_forall_exists_eq_add_mul.lean#L62-L80) — `flt-anthropic-0370`

Snippet: `samples/flt-anthropic/flt-anthropic-0370.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearIndependent.pair_iff'
- **file**: Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean
- **derivation**: exact (LinearIndependent.pair_iff' one_ne_zero).2 fun a h => ω_spec p (by rw [← h, Algebra.smul_def, mul_one]; exact pow_p_algebraMap p a)
- **explanation**: Mathlib's `LinearIndependent.pair_iff'` says that over a field, for x ≠ 0, `LinearIndependent K ![x, y] ↔ ∀ a : K, a • x ≠ y`. Taking K = ZMod p, x = 1 and y = ω p reduces the goal to showing `a • 1 ≠ ω p` for every a. That follows in one line from the library's own lemmas: `a • 1 = ι a`, `pow_p_algebraMap` and `ω_spec`. The current proof uses `LinearIndependent.pair_iff` instead and does a manual field computation. I searched Mathlib for lemmas about linear independence of `![1, x]`. I found no lemma that states the result directly, and none that ties it to `x` lying outside the image of the base field. The Unramified/Field.lean hit only uses such a pair inside another proof. The match is borderline, because the derivation does need the library's own `ω_spec` and `pow_p_algebraMap`, which carry the specific content about ω.

### [`P2MW.S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.ModularCurve.QExpN.liftPerm_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant.lean#L140-L142) — `flt-anthropic-0373`

Snippet: `samples/flt-anthropic/flt-anthropic-0373.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Equiv.Perm.decomposeFin_symm_apply_zero
- **file**: Mathlib/GroupTheory/Perm/Fin.lean
- **derivation**: Equiv.Perm.decomposeFin_symm_apply_zero 0 e
- **proof_uses_it**: True
- **explanation**: The library defines `liftPerm ℓ e := Equiv.Perm.decomposeFin.symm (0, e)`. The target `liftPerm ℓ e 0 = 0` is then Mathlib's `Equiv.Perm.decomposeFin_symm_apply_zero (p : Fin (n+1)) (e : Perm (Fin n)) : decomposeFin.symm (p, e) 0 = p` with `p = 0`, after unfolding `liftPerm`. The current proof is exactly this application.

### [`P2MW.S_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet.CosetDict.pr_mem_integers`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet.lean#L111-L111) — `flt-anthropic-0389`

Snippet: `samples/flt-anthropic/flt-anthropic-0389.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: natCast_mem
- **file**: Mathlib/Algebra/Ring/Subsemiring/Defs.lean
- **derivation**: natCast_mem (HeightOneSpectrum.adicCompletionIntegers ℚ v) (pr v : ℕ)
- **explanation**: The statement says that the natural number `pr v`, cast into the adic completion of ℚ at v, lies in `adicCompletionIntegers ℚ v`. That set is a `ValuationSubring (v.adicCompletion ℚ)`, and Mathlib has `instance : SubringClass (ValuationSubring K) K`. Mathlib's `natCast_mem` says every `(n : R)` lies in any `s : S` with `[AddSubmonoidWithOneClass S R]`, which a `SubringClass` gives. So the theorem is `natCast_mem` with `s` the valuation subring and `n := pr v`. The library's own proof calls a local `natCast_mem_integers`, which proves the same fact by hand using valuations. I did not search for other candidates beyond this one. I also did not check whether `adicCompletionIntegers` has an explicit `K` argument in this setting, so the derivation may need the explicit arguments adjusted.

### [`P2MW.S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.ModularCurve.WUniqLevelP.not_mem_nonunits_of_inv_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_DRModel_valuationSubring_pair_eq_gauss_and_exists_algEquiv_swap.lean#L105-L107) — `flt-anthropic-0394`

Snippet: `samples/flt-anthropic/flt-anthropic-0394.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ValuationSubring.mem_nonunits_iff_or
- **file**: Mathlib/RingTheory/Valuation/ValuationSubring.lean
- **derivation**: fun hn => ((ValuationSubring.mem_nonunits_iff_or).mp hn).elim ha0 (fun h' => h' h)
- **explanation**: Mathlib has `ValuationSubring.mem_nonunits_iff_or : x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A`. The target says that if a ≠ 0 and a⁻¹ ∈ A, then a ∉ A.nonunits. This is the contrapositive of the forward direction of that iff, so it follows in one line. The current proof uses `mem_nonunits_iff'`, a different lemma (probably a local one). I did not look it up.

### [`P2MW.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural.CycBaseKummerSurj.levelGal_surjective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural.lean#L55-L63) — `flt-anthropic-0399`

Snippet: `samples/flt-anthropic/flt-anthropic-0399.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgEquiv.restrictNormalHom_surjective
- **file**: Mathlib/FieldTheory/Normal/Basic.lean
- **derivation**: (AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)).comp (IntermediateField.fixingSubgroupEquiv K).surjective
- **proof_uses_it**: True
- **explanation**: `levelGal K L hKL` is defined as `(AlgEquiv.restrictNormalHom ↥(levelField K L hKL)).comp (IntermediateField.fixingSubgroupEquiv K).toMonoidHom`. Mathlib's `AlgEquiv.restrictNormalHom_surjective` (needs `Normal F K₁` and `Normal F E`) says the restriction map Gal(E/F) → K₁ ≃ₐ[F] K₁ is surjective. `fixingSubgroupEquiv K` is a `MulEquiv`, so it is surjective. The composite of two surjections is surjective, so the theorem follows after unfolding `levelGal`. The current proof does the same thing by hand: it takes a preimage with `restrictNormalHom_surjective` and pulls it back along `fixingSubgroupEquiv.symm`.

### [`P2MW.S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.HeckeEis.BolAux.coeff_pderiv_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv.lean#L22-L48) — `flt-anthropic-0401`

Snippet: `samples/flt-anthropic/flt-anthropic-0401.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPolynomial.coeff_pderiv
- **file**: Mathlib/Algebra/MvPolynomial/PDeriv.lean
- **derivation**: by rw [MvPolynomial.coeff_pderiv, mul_comm]; push_cast; rfl
- **explanation**: Mathlib's `MvPolynomial.coeff_pderiv` says `coeff m (pderiv i p) = coeff (m + single i 1) p * (m i + 1)` for any index type σ and commutative semiring R. The target is the case σ = Fin 2, i = 1, R = K. It differs only by the factor order (`mul_comm`) and the cast form `((d 1 + 1 : ℕ) : K)` versus `(d 1 : K) + 1` (`push_cast`). The current proof does its own induction on monomials.

### [`P2MW.S_jacobiTheta_two_eq_tprod.JTPEngine.qfact_succ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_jacobiTheta_two_eq_tprod.lean#L25-L27) — `flt-anthropic-0402`

Snippet: `samples/flt-anthropic/flt-anthropic-0402.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Finset.prod_range_succ
- **file**: Mathlib/Algebra/BigOperators/Basic.lean
- **derivation**: unfold qfact; exact Finset.prod_range_succ _ m
- **proof_uses_it**: True
- **explanation**: The library defines qfact Q m := ∏ i ∈ Finset.range m, (1 - Q ^ (i + 1)). The statement qfact Q (m+1) = qfact Q m * (1 - Q^(m+1)) is Finset.prod_range_succ (∏ x ∈ range (n+1), f x = (∏ x ∈ range n, f x) * f n) with f i = 1 - Q^(i+1), after unfolding the definition. The current proof is exactly this. I did not re-read the Mathlib file to confirm the path above; it is from memory.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one.dflip_mul_scalar`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_ne_zero_forall_eval_mul_eq_mul_rootNumber_mul_eval_of_forall_localZeta31_fe_twist_of_isCubicInductionDataOn_of_deep_of_archPackage_of_inv_eq_psiQ_of_whittakerLoc_one.lean#L1757-L1763) — `flt-anthropic-0416`

Snippet: `samples/flt-anthropic/flt-anthropic-0416.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.scalar_commute
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean
- **derivation**: (Matrix.GeneralLinearGroup.scalar_commute t dflip).symm
- **explanation**: Mathlib's `scalar_commute (u : Rˣ) (A : GL n R) : scalar n u * A = A * scalar n u` for a commutative ring R holds for every A. The theorem is the same statement with the sides swapped and A := dflip, over the field A. The library's proof computes entrywise with `fin_cases` and does not use this lemma.

### [`P2MW.S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.ModularCurve.ESDescent.conj_mem'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.lean#L200-L203) — `flt-anthropic-0421`

Snippet: `samples/flt-anthropic/flt-anthropic-0421.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.normal_subgroupOf_iff
- **file**: Mathlib/Algebra/Group/Subgroup/Basic.lean
- **derivation**: by simpa using (Subgroup.normal_subgroupOf_iff hle).mp hn γ (δ : SL(2, ℤ))⁻¹ hγ (Γ.inv_mem δ.2)
- **proof_uses_it**: True
- **explanation**: Mathlib's `Subgroup.normal_subgroupOf_iff (hHK : H ≤ K) : (H.subgroupOf K).Normal ↔ ∀ h k, h ∈ H → k ∈ K → k * h * k⁻¹ ∈ H` is the general statement. The theorem is the case k = δ⁻¹, with H = Γ', K = Γ, G = SL(2,ℤ). After that, `inv_inv` finishes it, and `simpa` does that. The library's proof reaches it through the local `conj_mem`, which applies the same lemma. `conj_mem'` is the same statement with δ⁻¹ and δ swapped, so the derivation is one application plus `simpa`.

### [`P2MW.S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport.K6A.continuous_sG`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TwistedUnipotentTerm_isLocallyConstant_integral_setIntegral_integral_semiLocalCharacter_mul_twist_and_hasCompactSupport.lean#L247-L262) — `flt-anthropic-0426`

Snippet: `samples/flt-anthropic/flt-anthropic-0426.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Continuous.units_map
- **file**: Mathlib/Topology/Algebra/Monoid.lean
- **derivation**: exact Continuous.units_map _ (continuous_id.matrix_map (continuous_congr K L v σ))
- **explanation**: sG is Matrix.GeneralLinearGroup.map f, which by definition is Units.map (RingHom.mapMatrix f).toMonoidHom, where f is the (continuous) tensor-product automorphism congr σ id. Mathlib's Continuous.units_map says Units.map g is continuous whenever the monoid hom g is. Here g sends a matrix to Matrix.map f, which is continuous by Continuous.matrix_map and the library's lemma continuous_congr. So the theorem is a short instance of Continuous.units_map. The current proof instead redoes the argument with Units.continuous_iff, a separate step for the inverse, and an unfolding by hand. I did not check that the derivation elaborates, since I can't run Lean. I read Continuous.units_map and the definition of Matrix.GeneralLinearGroup.map in the sources.

### [`P2MW.S_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three.ModularCurve.O4Eng.transcendental_of_coe`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three.lean#L121-L123) — `flt-anthropic-0431`

Snippet: `samples/flt-anthropic/flt-anthropic-0431.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IntermediateField.isAlgebraic_iff
- **file**: Mathlib/FieldTheory/IntermediateField/Algebraic.lean
- **derivation**: fun K L _ _ _ E z h => IntermediateField.isAlgebraic_iff.not.mpr h  -- i.e. := IntermediateField.isAlgebraic_iff.not.mpr h
- **proof_uses_it**: True
- **explanation**: Mathlib has `IntermediateField.isAlgebraic_iff {x : S} : IsAlgebraic K x ↔ IsAlgebraic K (x : L)`. The target, `Transcendental K ↑z → Transcendental K z`, is the `mpr` direction of its negation, because `Transcendental` is defined as `¬ IsAlgebraic`. The library's current proof already uses it, with `.mp` and a lambda. Mathlib also has `Subalgebra.transcendental_iff_transcendental_val`, but that is stated for `Subalgebra`, not `IntermediateField`.

### [`P2MW.S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem.WhittakerPS2Ext.psi_ne_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_CubicInduction_exists_linearMap_forall_apply_principalSeries2Rep_upperUnipotent2_eq_mul_and_apply_eq_of_forall_mem.lean#L205-L208) — `flt-anthropic-0435`

Snippet: `samples/flt-anthropic/flt-anthropic-0435.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddChar.val_isUnit
- **file**: Mathlib/Algebra/Group/AddChar.lean
- **derivation**: (AddChar.val_isUnit ψ a).ne_zero
- **explanation**: `AddChar.val_isUnit` says that `φ a` is a unit for any additive character of an additive group into a monoid. Here the target is ℂ, which is a nontrivial monoid with zero, so `IsUnit.ne_zero` gives `ψ a ≠ 0`. The library's proof instead goes through its own lemma `psi_neg_mul_self`.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.CerednikDrinfeld.FormalOmega.T3Aux.mem_line_of_coordEquiv_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_IsAdicFrame_exists_v_eq_zpow.lean#L1233-L1239) — `flt-anthropic-0456`

Snippet: `samples/flt-anthropic/flt-anthropic-0456.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.mem_map_equiv
- **file**: Mathlib/Algebra/Module/Submodule/Map.lean
- **derivation**: by
  rw [lineCoord, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] at h
  exact h
- **explanation**: lineCoord x n is by definition `((x.pt n).line L).map (coordEquiv ..).toLinearMap`. The theorem says that if e y ∈ S.map e for a linear equivalence e, then y ∈ S. Mathlib's `Submodule.mem_map_equiv` states `x ∈ p.map (e : M →ₛₗ M₂) ↔ e.symm x ∈ p`. Taking x := e y and using `LinearEquiv.symm_apply_apply` gives the result. The library instead unfolds `Submodule.mem_map` and uses injectivity of the equivalence. I could not run Lean, so the `rw` chain is unchecked. In particular I haven't confirmed that `.toLinearMap` matches the coercion form `(e : M →ₛₗ M₂)` syntactically.

### [`P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section.MvPolynomial.CrossingQuotient.Resolution.torusLift_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPolynomial_CrossingQuotient_Resolution_isInvertible_ker_section.lean#L319-L321) — `flt-anthropic-0463`

Snippet: `samples/flt-anthropic/flt-anthropic-0463.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: IsLocalization.Away.lift_eq
- **file**: Mathlib/RingTheory/Localization/Away/Basic.lean
- **derivation**: IsLocalization.Away.lift_eq _ _ c
- **proof_uses_it**: True
- **explanation**: torusLift is defined as IsLocalization.Away.lift (algebraMap W (CrossingQuotient W t) t) (g := (algebraMap W (Localization.Away t)).comp (lift t a b h).toRingHom) _. The theorem is `IsLocalization.Away.lift_eq` (lift x hg (algebraMap R S a) = g a) with that specific g and R = CrossingQuotient W t, S = TorusRing t. The existing proof already is `IsLocalization.Away.lift_eq _ _ c` after unfolding the definition. The result is the defining equation of torusLift, so most of its content sits in the library's own definition, but the Mathlib lemma supplies the localization-lift property.

### [`P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_ofPoint_of_range_subset.SectInvAux.jV_snd`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_ofPoint_of_range_subset.lean#L29-L31) — `flt-anthropic-0472`

Snippet: `samples/flt-anthropic/flt-anthropic-0472.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.pullback.lift_snd
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean
- **derivation**: pullback.lift_snd _ _ _
- **proof_uses_it**: True
- **explanation**: `jV` is the library's own abbreviation for `pullback.map ...`, which Mathlib defines as a `pullback.lift` of `fst ≫ _` and `snd ≫ _`. Unfolding it, `jV_snd` is the instance of `pullback.lift_snd` that says the second projection of the lift equals `pullback.snd _ _ ≫ 𝟙 T`. The current proof is exactly `pullback.lift_snd _ _ _`. I found no dedicated `pullback.map_snd` lemma in Mathlib. The only candidate is the generic universal-property lemma, applied after unfolding `jV`. This is a borderline case: the statement is mostly a defining-equation lemma for the library's own `jV`.

### [`P2MW.S_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw.Ws26T4.isLocalHom_algebraMap_intClosure`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw.lean#L115-L126) — `flt-anthropic-0474`

Snippet: `samples/flt-anthropic/flt-anthropic-0474.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.IsIntegral.isLocalHom
- **file**: Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean
- **derivation**: haveI : FaithfulSMul ℤ_[q] (integralClosure ℤ_[q] Kw) := (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => FaithfulSMul.algebraMap_injective ℤ_[q] Kw (congrArg Subtype.val h)
exact Algebra.IsIntegral.isLocalHom ℤ_[q] (integralClosure ℤ_[q] Kw)
- **explanation**: The theorem says the structure map ℤ_[q] → integralClosure ℤ_[q] Kw is a local homomorphism. Mathlib has `Algebra.IsIntegral.isLocalHom (R S)`. It gives `IsLocalHom (algebraMap R S)` for any integral algebra `R → S` with `[FaithfulSMul R S]`. It does not need `S` to be local, so the `IsLocalRing` hypothesis here is unused on Mathlib's side. The theorem is the case R = ℤ_[q], S = integralClosure ℤ_[q] Kw.

For this case the integrality instance should be found automatically. The remaining input is faithfulness, i.e. injectivity of ℤ_[q] → Kw, which is also the injectivity hypothesis of `RingHom.IsIntegral.isLocalHom`. I did not find a Mathlib instance giving `FaithfulSMul` for this integral closure directly, so the derivation supplies it in one line. I could not run Lean, so that line is unchecked. In particular, it assumes `FaithfulSMul ℤ_[q] Kw` is available as an instance.

The library's proof does not use this lemma. It goes through the p-adic norm of units instead. I checked the statement of `Algebra.IsIntegral.isLocalHom` in the sources. I also searched Mathlib for other `IsLocalHom (algebraMap …)` results and for `FaithfulSMul` instances.

### [`P2MW.S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.ModularCurve.MultCovering.INF.coeff_coe_ratSmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_MultCovering_infChart_residue_eq_ssPolyBar_mul_of_orthogonal.lean#L59-L64) — `flt-anthropic-0478`

Snippet: `samples/flt-anthropic/flt-anthropic-0478.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HahnSeries.coeff_smul
- **file**: Mathlib/RingTheory/HahnSeries/Addition.lean
- **derivation**: by
  have h : ((c • x : S) : LaurentSeries ℚ) = c • (x : LaurentSeries ℚ) := rfl
  rw [h, HahnSeries.coeff_smul, smul_eq_mul]
- **explanation**: HahnSeries.coeff_smul says (r • x).coeff a = r • x.coeff a for a Hahn series x. The theorem is this lemma with R = ℚ, V = ℚ, Γ = ℤ and the series ↑x. Two small steps remain. The coercion of c • x from the intermediate field S equals c • ↑x by rfl, which the current proof also uses. smul_eq_mul turns c • coeff into c * coeff. The current proof instead rewrites through HahnSeries.C and coeff_single_zero_mul. I did not run this derivation, since I can't run Lean. The Mathlib lemma does carry the mathematical content, and none of the lemmas it relies on depend on the target theorem.

### [`NumberField.ArchIdele.exists_above`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_NumberField_ArchimedeanIdeleModule.lean#L152-L153) — `flt-anthropic-0480`

Snippet: `samples/flt-anthropic/flt-anthropic-0480.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: NumberField.InfinitePlace.comap_surjective
- **file**: Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean
- **derivation**: InfinitePlace.comap_surjective v
- **proof_uses_it**: True
- **explanation**: Mathlib's `comap_surjective` states `Function.Surjective (comap · (algebraMap k K))` for an algebraic extension `K/k`. Unfolding `Surjective` gives exactly `∀ v, ∃ w, w.comap (algebraMap E K) = v`. The existing proof is already this one-line application, so the theorem is a restatement of it.

### [`P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex.LayerPlumbing.isOpen_setOf_isUnit_mixedSpace`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_ker_norm_integral_mul_log_sq_add_norm_resolvent_sq_eq_add_norm_sq_mul_log_mul_of_isComplex_isComplex.lean#L105-L112) — `flt-anthropic-0482`

Snippet: `samples/flt-anthropic/flt-anthropic-0482.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Units.isOpen
- **file**: Mathlib/Analysis/Normed/Ring/Units.lean
- **derivation**: Units.isOpen
- **explanation**: Units.isOpen says that in a normed ring with summable geometric series, {x | IsUnit x} is open. The target takes R := NumberField.mixedEmbedding.mixedSpace L. That is an abbrev for ({w // IsReal w} → ℝ) × ({w // IsComplex w} → ℂ). Mathlib has the instances Prod.normedRing and Pi.normedRing, and the Pi instance needs a Fintype index, which exists here. ℝ and ℂ are complete, so the product is complete and has summable geometric series. The topology of the resulting normed ring is the product topology, so the goal is exactly `Units.isOpen` at this type. I did not run Lean, so the instance unification is unchecked. The library's current proof instead rewrites the set as an intersection of coordinate-nonvanishing sets, using its own `isUnit_mixedSpace_iff`.

### [`P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ.StalkConstr.padicInt_exists_nat_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_stalkMap_tangent_germ.lean#L303-L308) — `flt-anthropic-0483`

Snippet: `samples/flt-anthropic/flt-anthropic-0483.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PadicInt.appr_spec
- **file**: Mathlib/NumberTheory/Padics/RingHoms.lean
- **derivation**: obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec n r)
exact ⟨r.appr n, c, by rw [← hc]; abel⟩
- **explanation**: `PadicInt.appr_spec n x : x - (x.appr n : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n}`, with `appr x n : ℕ`. Unfolding span-singleton membership as divisibility gives `x - appr x n = p^n * c`. Take `k = r.appr n` and `r' = c`, which gives the claimed statement. The library proves it instead via `ker_toZModPow` and `ZMod.val`. The Mathlib lemma already supplies the natural-number representative, so the derivation is a short rewrite.

### [`P2MW.S_ModularCurve_moduliPlace_restrictAlong_inclusion.P2MKcDegC6.addOrderOf_div_nsmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_moduliPlace_restrictAlong_inclusion.lean#L43-L48) — `flt-anthropic-0486`

Snippet: `samples/flt-anthropic/flt-anthropic-0486.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: addOrderOf_nsmul_addOrderOf_div
- **file**: Mathlib/GroupTheory/OrderOfElement.lean
- **derivation**: subst hg; exact addOrderOf_nsmul_addOrderOf_div hN hMN
- **explanation**: Mathlib has `orderOf_pow_orderOf_div` (hx : orderOf x ≠ 0) (hn : n ∣ orderOf x) : orderOf (x ^ (orderOf x / n)) = n, tagged `@[to_additive]` at line 423. Its additive version is `addOrderOf_nsmul_addOrderOf_div`. I inferred that name from the to_additive naming rules and did not find it by grep, because the generated name does not appear in the source text. The theorem's statement is this lemma with `addOrderOf g` replaced by `N`, which `hg` gives. So `subst hg` reduces it to the Mathlib statement. The current proof reaches the result with `addOrderOf_nsmul'` and `Nat` lemmas instead.

### [`P2MW.S_CuspForm_heckeLocal_exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd.GalTqSol.isTorsionFree_end`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_heckeLocal_exists_smul_eq_heckeT_and_apply_eq_trace_frobenius_of_not_dvd.lean#L287-L294) — `flt-anthropic-0489`

Snippet: `samples/flt-anthropic/flt-anthropic-0489.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: LinearMap.instIsTorsionFree (auto-named instance `Module.IsTorsionFree S (M →ₛₗ[σ₁₂] M')`)
- **file**: Mathlib/Algebra/Module/LinearMap/Basic.lean
- **derivation**: inferInstance
- **explanation**: The instance at line 106 of Mathlib/Algebra/Module/LinearMap/Basic.lean says `[Module.IsTorsionFree S M'] : Module.IsTorsionFree S (M →ₛₗ[σ₁₂] M')`, with `[SMulCommClass R' S M']`. Take S = R = R' = 𝒪, M = M' = V and σ = RingHom.id. Then `Module.End 𝒪 V` is `V →ₗ[𝒪] V`, and `SMulCommClass 𝒪 𝒪 V` holds because 𝒪 is commutative. So the theorem is exactly this instance, and `inferInstance` should prove it. I did not check the instance's exact auto-generated name. It is proved by `coe_injective.moduleIsTorsionFree _ coe_smul`, which does not depend on the theorem being judged.

### [`P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.OrdProj.mem_Jtor`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH.lean#L98-L99) — `flt-anthropic-0493`

Snippet: `samples/flt-anthropic/flt-anthropic-0493.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.mem_torsionBy_iff
- **file**: Mathlib/Algebra/Module/Torsion/Basic.lean
- **derivation**: Submodule.mem_torsionBy_iff _ _
- **proof_uses_it**: True
- **explanation**: Jtor M H p n is defined as (Submodule.torsionBy ℤ (JH M H) ((p^n : ℕ) : ℤ)).toAddSubgroup. Mathlib's Submodule.mem_torsionBy_iff states x ∈ torsionBy R M a ↔ a • x = 0 for general R, M and a. Taking R = ℤ, a = ((p^n : ℕ) : ℤ) and the module JH M H gives the theorem. Membership in the coerced AddSubgroup unfolds definitionally, and the existing proof is exactly this one-line application.

### [`P2MW.S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent_of_eq_two.E150I.isDiscreteValuationRing_of_ringEquiv`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent_of_eq_two.lean#L87-L98) — `flt-anthropic-0498`

Snippet: `samples/flt-anthropic/flt-anthropic-0498.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: RingEquivClass.isDiscreteValuationRing
- **file**: Mathlib/RingTheory/DiscreteValuationRing/Basic.lean
- **derivation**: RingEquivClass.isDiscreteValuationRing e
- **explanation**: Mathlib's `RingEquivClass.isDiscreteValuationRing` has the same hypotheses: A and B are commutative rings and domains, A is a DVR, and `e` is an equivalence. Its `e` is any `EquivLike` with `RingEquivClass`, and `A ≃+* B` is one such type. It concludes `IsDiscreteValuationRing B`, which is the target statement. The library's proof does not use it. It rebuilds the result by hand from `IsPrincipalIdealRing.of_surjective` and `IsLocalRing.of_surjective'`.

### [`P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.isHomogeneous_of_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.lean#L86-L88) — `flt-anthropic-0499`

Snippet: `samples/flt-anthropic/flt-anthropic-0499.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPolynomial.mem_homogeneousSubmodule
- **file**: Mathlib/RingTheory/MvPolynomial/Homogeneous.lean
- **derivation**: (MvPolynomial.mem_homogeneousSubmodule d _).mp F.2
- **proof_uses_it**: True
- **explanation**: Mathlib has `mem_homogeneousSubmodule (n) (p) : p ∈ homogeneousSubmodule σ R n ↔ p.IsHomogeneous n` (proved by `Iff.rfl`). The theorem is its `.mp` applied to the membership proof `F.2` of the subtype element `F`. The current proof is exactly this one-line application.

### [`P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate.ModularCurve.DivisorFunction.ofComplex_coe`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate.lean#L29-L29) — `flt-anthropic-0509`

Snippet: `samples/flt-anthropic/flt-anthropic-0509.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: UpperHalfPlane.ofComplex_apply
- **file**: Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean
- **derivation**: ofComplex_apply τ
- **proof_uses_it**: True
- **explanation**: Mathlib's `UpperHalfPlane.ofComplex_apply (z : ℍ) : ofComplex (z : ℂ) = z` is the same statement. The library's proof is exactly `ofComplex_apply τ`, so the theorem is just a renamed copy.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_mul_integral_transposeInvN_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_of_forall_integral_localZeta31_dualWhittakerFn3_eq_of_torusShell.KcR5D.log_qR_pos`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_mul_integral_transposeInvN_mul_whittaker_iotaGL_diagUnits2_longWeyl3_eq_of_forall_integral_localZeta31_dualWhittakerFn3_eq_of_torusShell.lean#L87-L87) — `flt-anthropic-0533`

Snippet: `samples/flt-anthropic/flt-anthropic-0533.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: NumberField.HeightOneSpectrum.one_lt_absNorm
- **file**: Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean
- **derivation**: Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm p)
- **explanation**: The theorem says 0 < log (absNorm p.asIdeal : ℝ) for a height-one prime p of 𝓞 ℚ. Mathlib's `NumberField.HeightOneSpectrum.one_lt_absNorm` says 1 < absNorm v.asIdeal in ℕ for v : HeightOneSpectrum R, with R a Dedekind domain that is finite and free over ℤ. 𝓞 ℚ meets those assumptions. Casting to ℝ and applying `Real.log_pos` gives the theorem. The current proof applies `Real.log_pos` to the library's own `one_lt_qR` (not read), so it does not use the Mathlib lemma. I found no Mathlib lemma that states the log positivity directly, so this is a one-line special case and not a duplicate.

### [`P2MW.S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite.hensSplit_isMaximal_map_mk`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite.lean#L19-L26) — `flt-anthropic-0542`

Snippet: `samples/flt-anthropic/flt-anthropic-0542.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Ideal.IsMaximal.map_of_surjective_of_ker_le
- **file**: Mathlib/RingTheory/Ideal/Maps.lean
- **derivation**: haveI := hm; exact Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by simpa using hK)
- **explanation**: Mathlib's lemma says that if f is surjective, m is maximal and ker f ≤ m, then m.map f is maximal. Taking f = Ideal.Quotient.mk K gives the target statement. The kernel of that map is K (Ideal.mk_ker), so the hypothesis ker f ≤ m is exactly hK. The library's proof reproduces Mathlib's proof, which uses map_eq_top_or_isMaximal_of_surjective.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional.KW47.ofReal_zpow_cpow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_forall_rsLocalIntegral22_schwartz_centralCleared_laurentFE_of_principalSeries2_of_forall_torusZeta_fe_of_borelEigenfunctional.lean#L4601-L4612) — `flt-anthropic-0543`

Snippet: `samples/flt-anthropic/flt-anthropic-0543.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Complex.cpow_mul_ofReal_nonneg
- **file**: Mathlib/Analysis/SpecialFunctions/Pow/Real.lean
- **derivation**: by simpa [Real.rpow_intCast] using (Complex.cpow_mul_ofReal_nonneg hq.le (j : ℝ) z).symm
- **explanation**: Mathlib has `Complex.cpow_mul_ofReal_nonneg {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (z : ℂ) : (x : ℂ) ^ (↑y * z) = (↑(x ^ y) : ℂ) ^ z`, where `x ^ y` is the real power `rpow`. Take x = q and y = (j : ℝ). Then `Real.rpow_intCast` turns `q ^ (j : ℝ)` into `q ^ j` (zpow), and `Complex.ofReal_intCast` turns `((j : ℝ) : ℂ)` into `(j : ℂ)`. The result is the target with its two sides swapped. I could not run Lean, so I did not check that `simpa` closes the goal. The current proof does not use this lemma. It unfolds `cpow_def_of_ne_zero` and works with logs. I also checked `Complex.cpow_int_mul` and `Complex.cpow_intCast`. They only give `x ^ (n * y) = (x ^ y) ^ n`, which is a different statement.

### [`P2MW.S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar.P2mKindSignCx.ridE_lamE`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_isSigmaConjugate_scalar_conjAe_iff_pos_of_isNormConjugator_scalar.lean#L85-L86) — `flt-anthropic-0555`

Snippet: `samples/flt-anthropic/flt-anthropic-0555.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.TensorProduct.rid_tmul
- **file**: Mathlib/RingTheory/TensorProduct/Maps.lean
- **derivation**: (Algebra.TensorProduct.rid_tmul (R := ℝ) (S := ℝ) (A := ℂ) 1 l).trans (one_smul ℝ l)  -- after `unfold lamE ridE` / `show`, since ridE is by definition `Algebra.TensorProduct.rid ℝ ℝ ℂ`
- **explanation**: ridE is defined as the ring-equiv underlying `Algebra.TensorProduct.rid ℝ ℝ ℂ` on `ℂ ⊗[ℝ] ℝ`, and lamE l = l ⊗ₜ 1. So the statement is `rid (l ⊗ₜ 1) = l`. Mathlib's `Algebra.TensorProduct.rid_tmul` gives `rid R S A (a ⊗ₜ r) = r • a` (proved by rfl), and `one_smul` finishes it. The library's own `ridE_tmul` is the same lemma, proved by rfl. Equivalently, `Algebra.TensorProduct.rid_symm_apply` gives `rid.symm l = l ⊗ₜ 1`. The current proof uses the library's `ridE_tmul` plus `one_smul`, not the Mathlib lemma directly. I did not check that the unfolding goes through.

### [`P2MW.S_FreyPackage_frey_wild_inertia_at_two_trivial.FreyWild.one_lt_mul_self`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_wild_inertia_at_two_trivial.lean#L23-L24) — `flt-anthropic-0562`

Snippet: `samples/flt-anthropic/flt-anthropic-0562.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: one_lt_mul_self_iff
- **file**: Mathlib/Algebra/Order/Monoid/Defs.lean
- **derivation**: one_lt_mul_self_iff.mpr h
- **explanation**: Mathlib has `one_lt_mul_self_iff : 1 < a * a ↔ 1 < a`, stated for a linearly ordered commutative monoid with `IsOrderedMonoid`. `LinearOrderedCommGroupWithZero` provides these instances via `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`, so the lemma applies directly. The theorem is the `.mpr` direction. The current proof uses `lt_mul_self` and `lt_trans` instead.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.SesAffine.app_naturality`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_surjective_app_of_shortExact_of_locallyTrivial.lean#L37-L42) — `flt-anthropic-0578`

Snippet: `samples/flt-anthropic/flt-anthropic-0578.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PresheafOfModules.naturality_apply
- **file**: Mathlib/Algebra/Category/ModuleCat/Presheaf.lean
- **derivation**: exact (PresheafOfModules.naturality_apply φ.val.val i.op m).symm
- **explanation**: `Scheme.Modules.Hom.app φ U` is defined as `(forget₂ _ _).map (φ.val.app (.op U))`, where `φ.val.val` is a morphism of presheaves of modules. `PresheafOfModules.naturality_apply f g x` says `f.app Y (M₁.map g x) = M₂.map g (f.app X x)`. Taking `f = φ.val.val`, `g = i.op` and `x = m`, with `.symm`, gives the target statement up to definitional unfolding of `Hom.app` and `Scheme.Modules.presheaf`. An alternative is `(CategoryTheory.congr_fun (φ.mapPresheaf.naturality i.op) m).symm`, which uses `NatTrans.naturality` on `Scheme.Modules.Hom.mapPresheaf`. I found no Mathlib lemma stating this naturality directly for `Scheme.Modules.Hom.app`. I searched `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean` and `Tilde.lean`, and `Mathlib/Algebra/Category/ModuleCat/Presheaf.lean`. The current proof goes through `PresheafOfModules.Hom.naturality` and `LinearMap.congr_fun`, not `naturality_apply`.

### [`P2MW.S_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand.DBetaBar.one_mem_strictPeriods_bot`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand.lean#L44-L46) — `flt-anthropic-0588`

Snippet: `samples/flt-anthropic/flt-anthropic-0588.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem
- **file**: Mathlib/NumberTheory/ModularForms/Cusps.lean
- **derivation**: by rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]; exact AddSubgroup.mem_zmultiples _
- **proof_uses_it**: True
- **explanation**: Mathlib has `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hΓ : ModularGroup.T ∈ Γ) : strictPeriods (Γ : Subgroup (GL (Fin 2) ℝ)) = AddSubgroup.zmultiples 1`. Take Γ to be `CohCarrier.GammaH M H`. `Γb M H` is an abbrev for its coercion to `GL (Fin 2) ℝ`. Then `1 ∈ zmultiples 1` by `AddSubgroup.mem_zmultiples`. The only extra input is `translation_mem_GammaH`, which belongs to the library's own definition of GammaH. I found no single Mathlib lemma that states `1 ∈ strictPeriods` for a subgroup containing T directly. The nearest are `strictPeriods_SL2Z` and `one_mem_strictPeriods_SL`, which are for the full group. Mathlib has nothing on `GammaH` (no grep hits in ModularForms).

### [`P2MW.S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.CerednikDrinfeld.Omega.GlobalCurrent.v_algebraMap_pos`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_Omega_exists_mem_ribbonKernel_and_v_apply_smul_eq_mul_zpow_stabWidth_of_isUnit_of_forall_isOfFinOrder.lean#L140-L142) — `flt-anthropic-0603`

Snippet: `samples/flt-anthropic/flt-anthropic-0603.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Valuation.pos_iff
- **file**: Mathlib/RingTheory/Valuation/Basic.lean
- **derivation**: (Valuation.pos_iff _).mpr ((map_ne_zero _).mpr
  ((map_ne_zero_iff _ (IsFractionRing.injective R K₀)).mpr hϖ.ne_zero))
- **explanation**: Mathlib's `Valuation.pos_iff : 0 < v x ↔ x ≠ 0` (for nontrivial Γ₀) gives the goal once the image of ϖ in K is shown to be nonzero. That follows from `Irreducible.ne_zero` and injectivity of the ring homs `algebraMap R K₀` and `algebraMap K₀ K`. The library's proof does the same with `lt_of_le_of_ne zero_le'` and `Valuation.ne_zero_iff` instead of `pos_iff`. Its nonvanishing step uses a local helper, `algebraMap_ne_zero_of_irreducible`, which is the same fact. I did not check that `map_ne_zero_iff` with `IsFractionRing.injective R K₀` elaborates as written, so the derivation is untested.

### [`P2MW.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff.PDivOrthCR.ev_tmul`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff.lean#L119-L121) — `flt-anthropic-0626`

Snippet: `samples/flt-anthropic/flt-anthropic-0626.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.TensorProduct.lift_tmul
- **file**: Mathlib/RingTheory/TensorProduct/Maps.lean
- **derivation**: Algebra.TensorProduct.lift_tmul _ _ _ c x
- **proof_uses_it**: True
- **explanation**: The library defines `ev p w φ z := Algebra.TensorProduct.lift φ z (fun _ _ => Commute.all _ _)`. `ev_tmul` is Mathlib's `Algebra.TensorProduct.lift_tmul`, with `f := φ`, `g := z` and the commutation hypothesis `Commute.all`. Unfolding `ev` gives the statement. The current proof is already this one-line application.

### [`P2MW.S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd.FALT.val_mapGL'`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularForm_heckeU_add_slash_alSlash_eq_alSlash_heckeU_add_slash_of_not_dvd.lean#L266-L268) — `flt-anthropic-0637`

Snippet: `samples/flt-anthropic/flt-anthropic-0637.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.SpecialLinearGroup.mapGL_coe_matrix
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean
- **derivation**: Matrix.SpecialLinearGroup.mapGL_coe_matrix (n := Fin 2) (R := ℤ) (S := ℝ) γ
- **explanation**: Mathlib's `mapGL_coe_matrix` states `((mapGL S g : GL n S) : Matrix n n S) = g.map (algebraMap R S)` for a general commutative ring R, R-algebra S and any n. The theorem is the instance R = ℤ, S = ℝ, n = Fin 2. The only difference is that Mathlib writes `g.map` as the SL-level map, which is coerced to a matrix. That is definitionally the same as `Matrix.map` on the coerced matrix, so `exact` closes the goal. The library proves it by `rfl`, and Mathlib proves its lemma by `rfl` too.

### [`P2MW.S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.SepDescAux.chartBC_fst`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_IsSeparated_exists_fg_subalgebra_of_isSeparated_pullback_snd.lean#L115-L116) — `flt-anthropic-0646`

Snippet: `samples/flt-anthropic/flt-anthropic-0646.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.pullback.lift_fst
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean
- **derivation**: pullback.lift_fst _ _ _
- **explanation**: `chartBC` is an abbrev for `pullback.map ...`, which is itself an abbrev for `pullback.lift (fst ≫ chart a b f) (snd ≫ 𝟙 Y) _`. The statement `chartBC a b f g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ chart a b f` is therefore `pullback.lift_fst` (`lift h k w ≫ fst = h`) with `h := fst ≫ chart a b f`. The `snd` component is `snd ≫ 𝟙 Y`, which `lift_fst` doesn't touch. The current proof is `simp [chartBC]`, which reaches the same result by applying this simp lemma. I read the `pullback.map` definition in the Mathlib source but did not read the `lift_fst` statement itself. The match rests on the standard form `lift h k w ≫ fst = h`. Mathlib has no dedicated `pullback.map_fst` lemma. The abbrev is unfolded on both sides, so `lift_fst` applies directly.

### [`P2MW.S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers.PDivINJK.htf_K`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_PDivisibleGroup_CartierDuality_linearIndependent_tateModule_padicComplex_of_norm_sub_le_of_ringOfIntegers.lean#L246-L252) — `flt-anthropic-0676`

Snippet: `samples/flt-anthropic/flt-anthropic-0676.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: mul_eq_zero
- **file**: Mathlib/Algebra/GroupWithZero/Defs.lean
- **derivation**: exact (mul_eq_zero.mp hx).resolve_left (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
- **proof_uses_it**: True
- **explanation**: The statement says that in the ring OK p K, a subalgebra of the field PadicAlgCl p, p * x = 0 implies x = 0. That follows from `mul_eq_zero` in a domain, because (p : OK p K) ≠ 0 in characteristic zero. The library's proof already uses `mul_eq_zero` and `Nat.cast`-style facts, after pushing the equation into the ambient field by hand. In Mathlib, `Subalgebra.noZeroDivisors` and `Subsemiring.instCharZero` supply the needed instances on the subalgebra. I did not confirm that a `CharZero` instance for a `Subalgebra` is found automatically, since I can't run Lean, so the derivation depends on that. I found no Mathlib lemma specifically about `(n : R) * x = 0`.

### [`P2MW.S_ModularCurve_JHNeronObjectAtP_mem_closure_gluedPic0_mk_configuredPair.WSwapGenH.inv_efib_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_JHNeronObjectAtP_mem_closure_gluedPic0_mk_configuredPair.lean#L39-L43) — `flt-anthropic-0679`

Snippet: `samples/flt-anthropic/flt-anthropic-0679.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.Scheme.hom_inv_apply
- **file**: Mathlib/AlgebraicGeometry/Scheme.lean
- **derivation**: haveI := 𝔛.efib_iso A hA ρ hρ
exact Scheme.hom_inv_apply (asIso (𝔛.efib A hA ρ hρ)) P
- **explanation**: Mathlib has `Scheme.hom_inv_apply (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x`, a simp lemma. The theorem says the same for a morphism `f` of schemes that is an isomorphism (via `efib_iso`), with `inv f` as the inverse. Taking `e := asIso f` gives `(asIso f).inv = inv f` and `(asIso f).hom = f` by definitional unfolding. Applying a scheme morphism to a point is definitionally its `.base` map, so the two forms agree. The library's own proof goes through `Scheme.Hom.comp_apply` and `IsIso.hom_inv_id`, not this lemma. I did not find a version of the lemma stated directly for `IsIso f`.

### [`P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm.R1G1COT.cusp_holo`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm.lean#L610-L611) — `flt-anthropic-0687`

Snippet: `samples/flt-anthropic/flt-anthropic-0687.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CuspFormClass.holo
- **file**: Mathlib/NumberTheory/ModularForms/Basic.lean
- **derivation**: CuspFormClass.holo F
- **explanation**: The theorem says a cusp form F : CuspForm Γ k is MDifferentiable as a function ℍ → ℂ; its proof is the structure field `CuspForm.holo'`. Mathlib's `CuspFormClass.holo` (a field of the class `CuspFormClass`) states `∀ f : F, MDiff (f : ℍ → ℂ)`, where `MDiff` is `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)`. The instance `CuspFormClass.cuspForm` makes it apply to `CuspForm Γ k`, and `CuspFormClass.holo F` closes the goal. The only differences are presentation: the structure field versus the class field, and the subgroup `Γ₁ℝ M` as `Γ`. The current proof uses the structure field `CuspForm.holo'`, not `CuspFormClass.holo`.

### [`P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices.AnnulusG1.le_map_sum_add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_UVCrossingModel_gaussOrder_sub_pred_eq_sSup_dominantIndices.lean#L265-L276) — `flt-anthropic-0699`

Snippet: `samples/flt-anthropic/flt-anthropic-0699.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddValuation.map_le_sum
- **file**: Mathlib/RingTheory/Valuation/Basic.lean
- **derivation**: exact tsub_le_iff_right.mp (v.map_le_sum fun k hk => tsub_le_iff_right.mpr (h k hk))
- **explanation**: Mathlib has `AddValuation.map_le_sum`: if `g ≤ v (f i)` for all `i ∈ s`, then `g ≤ v (∑ i ∈ s, f i)`. The target has an extra `+ w` on the right of each inequality. `ℕ∞` has `OrderedSub` (it is in the derive list in `Mathlib/Data/ENat/Basic.lean`, line 49), so `n ≤ x + w ↔ n - w ≤ x` by `tsub_le_iff_right`. Take `g := n - w`, apply `map_le_sum`, then convert back. The library's own proof is a direct induction using `AddValuation.map_add`. I did not run this derivation in Lean. The elaboration of `tsub_le_iff_right` for `ℕ∞` is unchecked.

### [`P2MW.S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.WChart.wBar_fst`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XHDRModelAtP_exists_chartAlgFin_algEquiv_iotaFin_comp_w_eq_of_atkinLehner_generic_of_unitsMap.lean#L44-L45) — `flt-anthropic-0701`

Snippet: `samples/flt-anthropic/flt-anthropic-0701.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.pullback.lift_fst
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean
- **derivation**: unfold wBar; exact pullback.lift_fst _ _ _
- **proof_uses_it**: True
- **explanation**: `wBar` is defined as `pullback.map _ _ _ _ 𝔓.w.hom (𝟙 _) (𝟙 _) ..`. In Mathlib `pullback.map` is an abbrev for `pullback.lift (fst ≫ f₁') (snd ≫ f₂') _`. So the statement `wBar ≫ fst = fst ≫ w.hom` is `pullback.lift_fst` after unfolding the definition. This is also the `pullback.map` fst-projection property. I found no separately named `pullback.map_fst` lemma in Mathlib. The library's own proof already uses `pullback.lift_fst`. The theorem's content is the definition of `wBar` plus the generic pullback API lemma.

### [`P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries.isNoetherianRing_fin`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvPowerSeries_isNoetherianRing_fin.lean#L242-L248) — `flt-anthropic-0710`

Snippet: `samples/flt-anthropic/flt-anthropic-0710.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPowerSeries.isNoetherianRing
- **file**: Mathlib/RingTheory/MvPowerSeries/Equiv.lean
- **derivation**: inferInstance
- **explanation**: Mathlib has `instance MvPowerSeries.isNoetherianRing [Finite σ] : IsNoetherianRing (MvPowerSeries σ S)` for Noetherian commutative ring S. Taking σ = Fin n (which has a Finite instance) gives the theorem. Mathlib's own proof goes through a private lemma `isNoetherianRing_fin` that is the same statement, but the public instance covers it. The library's proof does the same induction by hand.

### [`P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic.PMDND.norm_iteratedFDeriv_dir_le`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic.lean#L211-L225) — `flt-anthropic-0727`

Snippet: `samples/flt-anthropic/flt-anthropic-0727.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: norm_iteratedFDeriv_clm_apply_const
- **file**: Mathlib/Analysis/Calculus/ContDiff/Bounds.lean
- **derivation**: have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ V y) := (contDiff_infty_iff_fderiv.1 hV).2
simpa only [norm_iteratedFDeriv_fderiv] using norm_iteratedFDeriv_clm_apply_const (f := fun y => fderiv ℝ V y) (c := w) (x := p) (n := j) hfd.contDiffAt (by exact_mod_cast le_top)
- **explanation**: In the library, `dir w V = fun p => fderiv ℝ V p w`. The lemma is therefore the bound ‖iteratedFDeriv j (fun y => fderiv V y w) p‖ ≤ ‖w‖ * ‖iteratedFDeriv j (fderiv V) p‖, followed by ‖iteratedFDeriv j (fderiv V) p‖ = ‖iteratedFDeriv (j+1) V p‖. Mathlib's `norm_iteratedFDeriv_clm_apply_const` gives the first step with f = fderiv ℝ V and c = w, assuming only ContDiffAt and n ≤ N. `norm_iteratedFDeriv_fderiv` (FTaylorSeries.lean) gives the second. The library's proof re-proves the first step by hand: it composes with `ContinuousLinearMap.apply` and bounds the operator norm, which is exactly how Mathlib proves `norm_iteratedFDeriv_clm_apply_const`. I did not find a Mathlib lemma about `dir` itself, since `dir` is the library's own definition.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.S3GlueKit.mem_imS_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd.lean#L50-L57) — `flt-anthropic-0746`

Snippet: `samples/flt-anthropic/flt-anthropic-0746.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Subring.mem_map_equiv
- **file**: Mathlib/Algebra/Ring/Subring/Basic.lean
- **derivation**: Subring.mem_map_equiv
- **explanation**: In the library, `imS e O` is defined as `O.map e.toRingHom`. `e.toRingHom` is the coercion `(e : K →+* L)`, so `mem_imS_iff` unfolds to `y ∈ O.map (e : K →+* L) ↔ e.symm y ∈ O`. That is exactly `Subring.mem_map_equiv`. The statement is general over rings, with `f : R ≃+* S`, so it applies to the fields K and L as they are. I did not check the definition of `imS` in the target file itself. I read the definition from a sibling file that has a near-identical `mem_imS_iff`: `P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_chartPole_otherPole_levelField_of_fixedField_of_algEquiv_linkedScalars_of_eq_three_of_dvd.lean`.

### [`P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable.S12EL.Int.den_eq_one_of_eq_intCast`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_PlaceSpecialization_ProlongationTuple_AnnulusDatumQ_den_circleDeg_eq_one_and_den_depthMoment_eq_one_of_inertiaStable.lean#L115-L116) — `flt-anthropic-0753`

Snippet: `samples/flt-anthropic/flt-anthropic-0753.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Rat.den_intCast
- **file**: Init/Data/Rat/Lemmas.lean
- **derivation**: h ▸ Rat.den_intCast m
- **proof_uses_it**: True
- **explanation**: The theorem says that if x = (m : ℚ) for an integer m, then x.den = 1. Lean core's `Rat.den_intCast (a : Int) : (a : Rat).den = 1` gives the denominator of an integer cast. The theorem follows by substituting x = m, which is just an equality rewrite. The library's proof does exactly this (`rw [h]; exact Rat.den_intCast m`). Mathlib's `Rat.den_eq_one_iff` also relates denominator 1 to being an integer, but it was not needed.

### [`P2MW.S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero.P2MG3b.mem_span_X_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Polynomial_abv_coeff_mul_pow_le_of_evalEval_C_add_X_eq_zero.lean#L117-L119) — `flt-anthropic-0761`

Snippet: `samples/flt-anthropic/flt-anthropic-0761.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PowerSeries.X_dvd_iff
- **file**: Mathlib/RingTheory/PowerSeries/Basic.lean
- **derivation**: by rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
- **proof_uses_it**: True
- **explanation**: The theorem says f ∈ span {X} ↔ constantCoeff f = 0. Mathlib's PowerSeries.X_dvd_iff states X ∣ φ ↔ constantCoeff φ = 0. Ideal.mem_span_singleton turns membership in a principal ideal into divisibility, so the theorem is X_dvd_iff plus that one-line rewrite. I found no Mathlib lemma that states the span-membership form directly. PowerSeries.span_X_isPrime proves the same equality inline, and Polynomial.ker_constantCoeff is the polynomial analogue. Because the derivation needs both X_dvd_iff and mem_span_singleton, this is a borderline case.

### [`P2MW.S_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero.R1AF8D2b.exists_sub_of_mem_map`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_NodeAnnulusEngine_toNat_ord_eq_length_localizedModule_of_forall_iff_evalAt_eq_zero.lean#L693-L733) — `flt-anthropic-0770`

Snippet: `samples/flt-anthropic/flt-anthropic-0770.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AdicCompletion.ker_evalOneₐ_eq_map
- **file**: Mathlib/RingTheory/AdicCompletion/Completeness.lean
- **derivation**: obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I x)
exact ⟨a, by rw [← AdicCompletion.ker_evalOneₐ_eq_map I I.fg_of_isNoetherianRing]; simp [RingHom.mem_ker, ha]⟩
- **explanation**: Mathlib has `AdicCompletion.ker_evalOneₐ_eq_map (fg : I.FG) : RingHom.ker (evalOneₐ I).toRingHom = I.map (algebraMap R (AdicCompletion I R))`. The target says that every x in the completion is congruent to some `of I A a` modulo `I.map (algebraMap …)`. Pick `a` as a lift of `evalOneₐ I x : A ⧸ I`. Then `x - of a` lies in the kernel of `evalOneₐ`, because `evalOneₐ_of` is `rfl`. The kernel equals `I.map (algebraMap …)` by the Mathlib lemma, using `I.fg_of_isNoetherianRing` for finite generation. I have not compiled the derivation. The library's own proof goes through the tensor-product and exactness route instead. It does not use this lemma.

### [`P2MW.S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt.FlatK1LC.det_apply_baseChangeAlong`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GaloisRep_DeformationRingData_length_cotangent_le_add_of_flatCondition_insert_isUnipotentOnInertiaAt.lean#L43-L48) — `flt-anthropic-0771`

Snippet: `samples/flt-anthropic/flt-anthropic-0771.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.det_baseChange
- **file**: Mathlib/LinearAlgebra/Charpoly/BaseChange.lean
- **derivation**: letI : Algebra A B := φ.toAlgebra
exact LinearMap.det_baseChange (ρ.ρ σ)
- **proof_uses_it**: True
- **explanation**: The library's `GaloisRepAdic.baseChangeAlong φ hφ ρ` has underlying map `σ ↦ (ρ.ρ σ).baseChange B` for the algebra structure `φ.toAlgebra`. By unfolding, the goal becomes `LinearMap.det (f.baseChange B) = algebraMap A B (LinearMap.det f)` with `f = ρ.ρ σ`. That is exactly `LinearMap.det_baseChange`, which says the determinant of a base-changed linear map is the image of the determinant under `algebraMap`. The current proof already does this with a `show` and an `exact`. I did not look for a library-specific version in Mathlib, since none could exist for `GaloisRepAdic`.

### [`P2MW.S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.Conj6.Qc_eq_zero_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_XOneP_ringEquiv_algEquiv_symm_eq_algEquiv_diamond_of_generatorLaw_x1_mul.lean#L203-L205) — `flt-anthropic-0773`

Snippet: `samples/flt-anthropic/flt-anthropic-0773.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModularForm.qExpansion_eq_zero_iff
- **file**: Mathlib/NumberTheory/ModularForms/QExpansion.lean
- **derivation**: rw [Qc, map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective, ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_Γ1 F]
- **proof_uses_it**: True
- **explanation**: Qc F is by definition the image of `qExpansion 1 F` under `HahnSeries.ofPowerSeries`, which is injective. The statement therefore reduces to `ModularForm.qExpansion_eq_zero_iff` with h = 1 and Γ = Γ1 N. That lemma states `qExpansion h f = 0 ↔ f = 0` for `f : ModularForm Γ k`, given `0 < h` and `h ∈ Γ.strictPeriods`. The library's proof is exactly this instantiation plus the injectivity step, which is routine. The local lemma `one_mem_strictPeriods_Γ1` is proved by `simp`, so it counts as a side goal closed by `simp`. I found no Mathlib lemma that states the Laurent-series version directly, because `Qc` is a local definition.

### [`P2MW.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.FrickeSpan.mdifferentiable_disc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top.lean#L52-L52) — `flt-anthropic-0777`

Snippet: `samples/flt-anthropic/flt-anthropic-0777.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModularFormClass.holo
- **file**: Mathlib/NumberTheory/ModularForms/Basic.lean
- **derivation**: exact ModularFormClass.holo CuspForm.discriminant
- **explanation**: The theorem says the modular discriminant Δ : ℍ → ℂ is MDifferentiable. In Mathlib, `ModularForm.discriminant` is the underlying function of the cusp form `CuspForm.discriminant` (`coe_discriminant : discriminant = Δ := rfl`). The class field `ModularFormClass.holo` states `∀ f : F, MDiff (f : ℍ → ℂ)`, and `CuspForm.discriminant` has a `ModularFormClass` instance through `CuspFormClass` (Basic.lean:129). Applying it to `CuspForm.discriminant` gives the statement up to a definitional unfolding. The current proof uses the structure field `CuspForm.holo'` directly, and `ModularFormClass.holo` is the class-level version of that field. I found no separate Mathlib lemma stating `MDifferentiable … Δ`.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le.P2mWs11RBC.op_hom_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le.lean#L18-L19) — `flt-anthropic-0778`

Snippet: `samples/flt-anthropic/flt-anthropic-0778.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.subsingleton_of_unop
- **file**: Mathlib/CategoryTheory/Opposites.lean
- **derivation**: Subsingleton.elim i j
- **explanation**: The theorem says any two morphisms op U ⟶ op V in the opposite of the poset category of opens are equal. Mathlib has the instance `CategoryTheory.subsingleton_of_unop`: `[Subsingleton (unop B ⟶ unop A)] → Subsingleton (A ⟶ B)` for objects of Cᵒᵖ. The unop hom type `V ⟶ U` in `Y.Opens` is a subsingleton, as the library's own proof shows by using `Subsingleton.elim` on it. So the instance applies directly and `Subsingleton.elim i j` proves the statement. The current proof instead goes through `Quiver.Hom.unop_inj`, which does not use the instance.

### [`P2MW.S_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow.H34A.pmap_some`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow.lean#L53-L57) — `flt-anthropic-0789`

Snippet: `samples/flt-anthropic/flt-anthropic-0789.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WeierstrassCurve.Affine.Point.map_some
- **file**: Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean
- **derivation**: exact WeierstrassCurve.Affine.Point.map_some (W' := W) (Algebra.ofId K F) h
- **explanation**: The local `pmap W` is defined as `WeierstrassCurve.Affine.Point.baseChange K F`, an abbrev for `Point.map (Algebra.ofId K F)`. Mathlib's `Point.map_some` says `map f (some _ _ h) = some _ _ ((baseChange_nonsingular f.injective ..).mpr h)`. Taking `f = Algebra.ofId K F` gives exactly this statement. Mathlib's `map_some` is proved by `rfl`, as is the local theorem. The two differ only by unfolding definitions, since `W.map (algebraMap K F)` is `W.baseChange F`, and by proof irrelevance of the nonsingularity proof. I could not run Lean, so I did not check that the `exact` elaborates.

### [`P2MW.S_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj.TwPT.algebraMap_withAbs_apply`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj.lean#L71-L73) — `flt-anthropic-0806`

Snippet: `samples/flt-anthropic/flt-anthropic-0806.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: WithAbs.ofAbs_algebraMap
- **file**: Mathlib/Analysis/Normed/Ring/WithAbs.lean
- **derivation**: exact WithAbs.ofAbs_injective _ (WithAbs.ofAbs_algebraMap v.1 w.1 x)
- **explanation**: Mathlib's `WithAbs.ofAbs_algebraMap` (v : AbsoluteValue R S) (w : AbsoluteValue T S) (x : WithAbs v) says `(algebraMap (WithAbs v) (WithAbs w) x).ofAbs = algebraMap R T x.ofAbs`. This is the target statement with R := K, T := L, v := v.1, w := w.1. The target writes `ofAbs` as `WithAbs.equiv`, which has the same underlying function as `ofAbs`, and `(equiv w).symm` is the inverse of `equiv w`. So the target equation is that Mathlib equation after applying the injectivity of `ofAbs` and unfolding these definitions, which are all defeq (the target's own proof is `rfl`). I didn't find a Mathlib statement phrased with `equiv`/`.symm`, so I'm giving this as a special case rather than a duplicate. Related Mathlib lemmas are `WithAbs.algebraMap_left_apply` and `WithAbs.algebraMap_right_apply`.

### [`P2MW.S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint.R4GC.C_eq_algebraMap`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_modularForm_gammaH_levelH_weight_three_qExpansion_eq_cuspPoint.lean#L1522-L1523) — `flt-anthropic-0815`

Snippet: `samples/flt-anthropic/flt-anthropic-0815.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: HahnSeries.C_eq_algebraMap
- **file**: Mathlib/RingTheory/HahnSeries/Multiplication.lean
- **derivation**: congrFun (congrArg DFunLike.coe HahnSeries.C_eq_algebraMap) c
- **explanation**: In Mathlib, `LaurentSeries L` is an abbrev for `L⟦ℤ⟧ = HahnSeries ℤ L`, and its `Algebra L` instance is the generic HahnSeries instance. `HahnSeries.C_eq_algebraMap : C = algebraMap R R⟦Γ⟧` is the same statement as a RingHom equality, for any ordered Γ and commutative semiring R. The theorem is this lemma with Γ := ℤ, R := L, applied at `c`. The `Field` and `CharZero` hypotheses are not needed. The library's proof goes through `algebraMap_laurentSeries_eq_single` and `HahnSeries.C_apply` instead. The `rw [HahnSeries.C_eq_algebraMap]` form may also work.

### [`P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt.CartierExistenceIntSol.incl_injective`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_CartierModule_tangent_surjective_of_algebra_padicInt.lean#L421-L424) — `flt-anthropic-0826`

Snippet: `samples/flt-anthropic/flt-anthropic-0826.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPolynomial.map_injective
- **file**: Mathlib/Algebra/MvPolynomial/Basic.lean
- **derivation**: fun P Q h => MvPolynomial.map_injective _ (IsFractionRing.injective ℤ_[p] ℚ_[p]) (by simpa [incl_apply] using h)
- **proof_uses_it**: True
- **explanation**: I did not open the Mathlib file to confirm its path or the exact statement of `MvPolynomial.map_injective`. From memory it says: if `f : R →+* S` is injective, then `MvPolynomial.map f` is injective. `incl p` is `MvPolynomial.mapAlgHom (Algebra.ofId ℤ_[p] ℚ_[p])`, and the library's `incl_apply` shows it agrees with `MvPolynomial.map (algebraMap ℤ_[p] ℚ_[p])`. The theorem is therefore `map_injective` with `f = algebraMap ℤ_[p] ℚ_[p]`. Injectivity of that map is `IsFractionRing.injective`, which is also Mathlib. The existing proof already applies `map_injective` this way, so it is a short instantiation.

### [`ModularCurve.uvSwapEquiv_C`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_UVCrossingModel.lean#L64-L66) — `flt-anthropic-0829`

Snippet: `samples/flt-anthropic/flt-anthropic-0829.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MvPowerSeries.rename_C
- **file**: Mathlib/RingTheory/MvPowerSeries/Rename.lean
- **derivation**: MvPowerSeries.rename_C (Equiv.swap (0 : Fin 2) 1) w
- **proof_uses_it**: True
- **explanation**: uvSwapEquiv is defined as the ring equivalence from MvPowerSeries.renameEquiv with Equiv.swap 0 1, and it unfolds definitionally to MvPowerSeries.rename (swap 0 1) (the library's uvSwapEquiv_apply is rfl). Mathlib's `MvPowerSeries.rename_C (r : R) : rename f (C r) = C r` is the statement for an arbitrary f. Instantiating f with the swap gives the target. The current proof is already `rw [uvSwapEquiv_apply, MvPowerSeries.rename_C]`.

### [`P2MW.S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.K1aOfFinite.det_globalPoints`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_exists_measure_lintegral_translate_eq_mul_and_setLIntegral_le_mul_of_coversModCentre_of_finite.lean#L37-L42) — `flt-anthropic-0832`

Snippet: `samples/flt-anthropic/flt-anthropic-0832.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.GeneralLinearGroup.map_det
- **file**: Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean
- **derivation**: unfold globalPoints
exact Matrix.GeneralLinearGroup.map_det _ _
- **proof_uses_it**: True
- **explanation**: globalPoints is defined as Matrix.GeneralLinearGroup.map (algebraMap F 𝔸). Mathlib's map_det says det (map f g) = Units.map f (det g) for a ring hom f. Instantiating f := algebraMap F 𝔸 gives the theorem, after unfolding the definition. The `.toMonoidHom` coercion matches definitionally (the current proof closes it with rfl). The current proof already rewrites with this lemma.

### [`P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial.CerednikDrinfeld.QM.SpecialOfFEC.lp_comm`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_QM_FakeEllipticCurve_IsFormalModuleOf_isSpecial.lean#L117-L118) — `flt-anthropic-0833`

Snippet: `samples/flt-anthropic/flt-anthropic-0833.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Commute.map
- **file**: Mathlib/Algebra/Group/Commute/Hom.lean
- **derivation**: exact (Commute.all a a').map (lp X)
- **explanation**: `lp X` is a ring hom `Zp2 q →+* Matrix (Fin 2) (Fin 2) B`, so it is a `MulHomClass`. `Commute.map` says a multiplicative hom sends commuting elements to commuting elements. `Commute.all a a'` holds because `Zp2 q` is commutative. `Commute (lp X a) (lp X a')` unfolds to `lp X a * lp X a' = lp X a' * lp X a`. The library's proof uses `map_mul` and `mul_comm` instead. I did not confirm that `Zp2 q` is a commutative ring by reading its definition.

### [`P2MW.S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet.LevelU4.IsInt.add`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet.lean#L1145-L1148) — `flt-anthropic-0839`

Snippet: `samples/flt-anthropic/flt-anthropic-0839.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddSubmonoid.matrix
- **file**: Mathlib/Data/Matrix/Basic.lean
- **derivation**: exact add_mem (s := (v.adicCompletionIntegers ℚ).toSubring.toAddSubmonoid.matrix (m := Fin 2) (n := Fin 2)) hA hB
- **explanation**: `IsInt v A` unfolds to `∀ i j, A i j ∈ v.adicCompletionIntegers ℚ`, which is definitionally membership `A ∈ S.matrix` for the additive submonoid `S` underlying the valuation subring (`AddSubmonoid.matrix`, `Set.matrix`, in Mathlib/Data/Matrix/Basic.lean and Mathlib/LinearAlgebra/Matrix/Defs.lean). The theorem is therefore closure of `S.matrix` under addition, which Mathlib's `add_mem'` field proves by the same entrywise `add_mem` as the current proof. The match relies on unfolding `IsInt` and on definitional unfolding of `AddSubmonoid.matrix`. I could not run Lean to check that the derivation elaborates.

### [`P2MW.S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot.W1TW.mneZ`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_isLevelAutAt_conj_of_isLevelAutAt_of_isPrimitiveRoot.lean#L25-L25) — `flt-anthropic-0844`

Snippet: `samples/flt-anthropic/flt-anthropic-0844.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Nat.cast_ne_zero
- **file**: Mathlib/Algebra/CharZero/Defs.lean
- **derivation**: Nat.cast_ne_zero.mpr (NeZero.ne m)
- **explanation**: The statement is `(m : ℤ) ≠ 0` for `m : ℕ` with `[NeZero m]`. Mathlib's `Nat.cast_ne_zero` (`(n : R) ≠ 0 ↔ n ≠ 0` for `AddMonoidWithOne R` with `CharZero R`) gives it at `R = ℤ`, using `NeZero.ne m`. The instance `NeZero.charZero` (`NeZero (n : M)` from `NeZero n`) also gives it as `NeZero.ne (m : ℤ)`. I did not open the `Nat.cast_ne_zero` declaration itself. I only read its uses and the `NeZero.charZero` instance in `Mathlib/Algebra/CharZero/Defs.lean`, which show its form. The current proof uses `exact_mod_cast`, which reaches the same fact by norm_cast.

### [`P2MW.S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers.HeckeCartan.mem_integers_of_valued_le_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers.lean#L123-L124) — `flt-anthropic-0848`

Snippet: `samples/flt-anthropic/flt-anthropic-0848.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
- **file**: Mathlib/RingTheory/DedekindDomain/AdicValuation.lean
- **derivation**: (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hx
- **proof_uses_it**: True
- **explanation**: Mathlib's `mem_adicCompletionIntegers : x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1` (proved by `Iff.rfl`) gives this theorem by applying `.2`. The theorem is just the `.mpr` direction, specialised to R = 𝓞 ℚ and K = ℚ. The library's proof is exactly that application.

### [`ModularCurve.TatePoint.charZero_H`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_ModularCurve_CycSubRootBridge.lean#L23-L24) — `flt-anthropic-0852`

Snippet: `samples/flt-anthropic/flt-anthropic-0852.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: charZero_of_injective_ringHom
- **file**: Mathlib/Algebra/CharP/Algebra.lean
- **derivation**: charZero_of_injective_ringHom (HahnSeries.C (R := Qbar) (Γ := ℚ)).injective
- **explanation**: H is `HahnSeries ℚ Qbar`. Mathlib has no `CharZero` instance for `HahnSeries`; I found none in the HahnSeries files or in CharP. The library's proof applies `RingHom.charZero_iff` to the injective ring hom `HahnSeries.C`, together with `CharZero Qbar`. `charZero_of_injective_ringHom` states exactly the direction needed: for `f : R →+* A` injective with `[CharZero R]`, `CharZero A` holds. Instantiating it with `f = HahnSeries.C` gives the goal in one line. `inferInstance` supplies `CharZero Qbar`, as in the current proof. I did not check that `HahnSeries.C` has the type `Qbar →+* HahnSeries ℚ Qbar`, but the current proof already uses its `.injective` the same way. `RingHom.charZero_iff` (Mathlib/Algebra/Ring/CharZero.lean) is a sibling statement and would also work.

### [`P2MW.S_WeierstrassCurve_natCard_stabilizer_zmultiples_eq_natCard_stabilizer_zmultiples_fullKernelQuotient.P2MKcStabDual.nsmul_ne_zero_of_mem_Icc`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_WeierstrassCurve_natCard_stabilizer_zmultiples_eq_natCard_stabilizer_zmultiples_fullKernelQuotient.lean#L164-L166) — `flt-anthropic-0860`

Snippet: `samples/flt-anthropic/flt-anthropic-0860.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: nsmul_ne_zero_of_lt_addOrderOf
- **file**: Mathlib/GroupTheory/OrderOfElement.lean
- **derivation**: nsmul_ne_zero_of_lt_addOrderOf (by omega) (by rw [hQ]; omega)
- **proof_uses_it**: True
- **explanation**: The theorem is the additive version of `pow_ne_one_of_lt_orderOf`, namely `nsmul_ne_zero_of_lt_addOrderOf (n0 : n ≠ 0) (h : n < addOrderOf x) : n • x ≠ 0`. It is stated for any additive monoid. The theorem takes `1 ≤ k ≤ N - 1` and `addOrderOf Q = N` and applies that lemma with `x := Q`. The two side goals, `k ≠ 0` and `k < addOrderOf Q`, are closed by `omega`, after one `rw [hQ]` for the second. The current proof already uses this lemma.

### [`P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt.CerednikDrinfeld.FormalOmega.LevelAux.red_zero_eq_id`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt.lean#L136-L140) — `flt-anthropic-0876`

Snippet: `samples/flt-anthropic/flt-anthropic-0876.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.factorₐ_refl
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: Ideal.Quotient.factorₐ_refl (Ideal.span {algebraMap 𝒪 R π ^ (0 + 1)})
- **explanation**: `red π 0` is by definition `Ideal.Quotient.factorₐ 𝒪 (span_pow_le_span_one π 0)`, the factor map from R ⧸ span{π^(0+1)} to itself (the inequality proof is irrelevant). Mathlib's `Ideal.Quotient.factorₐ_refl` says that `factorₐ R (le_refl I) = AlgHom.id R _`. Instantiating I := span{algebraMap 𝒪 R π ^ (0+1)} gives the theorem, after unfolding `red` and `modPow`, which are defeq. The current proof does not use it. It uses `Ideal.Quotient.algHom_ext` and then `rfl`.

### [`P2MW.S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval.P2mResNorm.mem_span_pow_of_le`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_TateModule_charpoly_toMatrix_rep_eq_map_of_natCard_primaryComponent_ker_aeval.lean#L45-L48) — `flt-anthropic-0879`

Snippet: `samples/flt-anthropic/flt-anthropic-0879.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.span_singleton_le_span_singleton
- **file**: Mathlib/RingTheory/Ideal/Span.lean
- **derivation**: exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hML) h
- **explanation**: The statement says span{p^L} ⊆ span{p^M} for M ≤ L in ℤ_[p]. Mathlib's `Ideal.span_singleton_le_span_singleton` says span{x} ≤ span{y} ↔ y ∣ x, and `pow_dvd_pow` gives p^M ∣ p^L. Applying the first lemma to the second gives the result in one line. The current proof reaches the same divisibility with `Ideal.mem_span_singleton` and `pow_dvd_pow`. It does not use `Ideal.span_singleton_le_span_singleton`. The result is a trivial instance of the general ring fact.

### [`P2MW.S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot.LinkLift.hom_eval`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_IsGamma1Link_of_map_of_surjective_of_ker_pow_eq_bot.lean#L28-L30) — `flt-anthropic-0882`

Snippet: `samples/flt-anthropic/flt-anthropic-0882.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Polynomial.eval_map_apply
- **file**: Mathlib/Algebra/Polynomial/Eval/Defs.lean
- **derivation**: (Polynomial.eval_map_apply χ p a).symm
- **explanation**: Mathlib's `Polynomial.eval_map_apply (f) (x : R) : (p.map f).eval (f x) = f (p.eval x)` is the target statement with the two sides swapped. Mathlib's version works for semirings, so it covers the commutative rings here. The current proof rewrites with `eval_map` and `eval₂_at_apply`, which are the same ingredients Mathlib uses to prove `eval_map_apply`.

### [`P2MW.S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.AlgebraicCurve.BombieriLower.pow_q_eq_of_mem_k`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicCurve_exists_sub_le_sum_divisors_mul_card_places.lean#L683-L686) — `flt-anthropic-0900`

Snippet: `samples/flt-anthropic/flt-anthropic-0900.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: FiniteField.pow_card
- **file**: Mathlib/FieldTheory/Finite/Basic.lean
- **derivation**: haveI := Fintype.ofFinite k; rw [← hq, Nat.card_eq_fintype_card, FiniteField.pow_card]
- **proof_uses_it**: True
- **explanation**: FiniteField.pow_card says a ^ Fintype.card K = a for a finite GroupWithZero K (with a Fintype instance). The target is the same statement with the exponent written as p^n, where hq : Nat.card k = p^n, and with Finite k instead of Fintype k. The derivation builds a Fintype instance with Fintype.ofFinite, rewrites p^n back to Nat.card k, converts Nat.card to Fintype.card, and applies pow_card. That is the library's current proof. I found no Mathlib version of pow_card stated with Nat.card, and no version with Finite in place of Fintype. FiniteField.pow_card_pow has exponent q^n, which does not match p^n.

### [`P2MW.S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2.U2Dual.norm_le_one_iff_mem`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_forall_integrable_and_godementZeta2_transposeInv_matFourier22_eq_mul_twoVarZeta_fourierSlice_of_mem_principalSeries2.lean#L182-L184) — `flt-anthropic-0902`

Snippet: `samples/flt-anthropic/flt-anthropic-0902.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Valued.toNormedField.norm_le_one_iff
- **file**: Mathlib/Topology/Algebra/Valued/NormedValued.lean
- **derivation**: (Valued.toNormedField.norm_le_one_iff).trans (HeightOneSpectrum.mem_adicCompletionIntegers ..).symm
-- or: by rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact Valued.toNormedField.norm_le_one_iff
- **explanation**: The norm on the adic completion F is Mathlib's instNormedFieldValuedAdicCompletion, which is Valued.toNormedField. Mathlib's @[simp] lemma Valued.toNormedField.norm_le_one_iff gives ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1. Mathlib's HeightOneSpectrum.mem_adicCompletionIntegers (proved by Iff.rfl) gives x ∈ adicCompletionIntegers ↔ Valued.v x ≤ 1. Composing the two gives the theorem, specialised to K = ℚ. The library's proof goes through its own norm_le_norm_iff_v_le_v lemma instead.

### [`P2MW.S_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay.WindB.dotR_sub_right`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MeasureTheory_exists_forall_exists_clm_opNorm_le_noAtomicMass_forall_hasSum_fibre_mul_fourier_eq_apply_fourier_of_le_of_discrete_of_productFormula_of_fourier_decay.lean#L1248-L1249) — `flt-anthropic-0909`

Snippet: `samples/flt-anthropic/flt-anthropic-0909.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: dotProduct_sub
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: by simpa [dotR, dotProduct] using dotProduct_sub ξ x x'
- **explanation**: `dotR ξ x` is defined as `∑ i, ξ i * x i`, which is by definition Mathlib's `dotProduct ξ x` (`ξ ⬝ᵥ x`) on `Fin r → ℝ`. `dotProduct_sub : u ⬝ᵥ (v - w) = u ⬝ᵥ v - u ⬝ᵥ w` (in a non-unital non-associative ring) is exactly the statement once `dotR` is unfolded. Specialised to `ℝ` and `Fin r`. I did not read the library's proof beyond the one-line `simp only`, which doesn't use it.

### [`P2MW.S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_transition_mul_mul.PV6R1.opHom_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_forall_transition_eq_transition_mul_mul.lean#L21-L22) — `flt-anthropic-0934`

Snippet: `samples/flt-anthropic/flt-anthropic-0934.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.subsingleton_of_unop
- **file**: Mathlib/CategoryTheory/Opposites.lean
- **derivation**: Subsingleton.elim f g
- **explanation**: The theorem says any two morphisms in (Y.Opens)ᵒᵖ are equal, i.e. Hom-sets there are subsingletons. Mathlib has the instance `CategoryTheory.subsingleton_of_unop`: Subsingleton (unop B ⟶ unop A) gives Subsingleton (A ⟶ B) in Cᵒᵖ. It combines with `CategoryTheory.subsingleton_hom` (Mathlib/CategoryTheory/Category/Preorder.lean:52), which makes Hom-sets of a preorder subsingletons. Y.Opens is a preorder, so instance inference finds both and `Subsingleton.elim f g` closes the goal. The current proof uses the same instance indirectly by going through `Quiver.Hom.unop_inj`, so it is essentially the same argument.

### [`P2MW.S_UnipotentTermUnfolding_exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization.AutomorphicForm.TwistedBruhat.mulVec_eq_smul_iff`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_UnipotentTermUnfolding_exists_forall_integrableOn_and_lintegral_ne_top_and_setIntegral_unipotentTerm_eq_mul_integral_iwasawa_of_isSemiLocalFactorization.lean#L1703-L1711) — `flt-anthropic-0950`

Snippet: `samples/flt-anthropic/flt-anthropic-0950.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.mulVec_fin_two
- **file**: Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean
- **derivation**: by rw [Matrix.mulVec_fin_two, funext_iff, Fin.forall_fin_two]; simp
- **explanation**: Mathlib has no lemma stating the eigenvector equation M *ᵥ w = c • w for 2×2 matrices as a pair of scalar equations. It does have `Matrix.mulVec_fin_two`, which rewrites `m *ᵥ v` as `![m 0 0 * v 0 + m 0 1 * v 1, m 1 0 * v 0 + m 1 1 * v 1]` for any semiring. The target then follows by rewriting with it, applying function extensionality (`funext_iff`) and splitting the two coordinates with `Fin.forall_fin_two`, which `simp` finishes. I could not run Lean, so this derivation is unchecked. I also searched Mathlib for `mulVec_eq_smul` and similar names and found nothing. The match is weak, because the theorem is mostly a coordinate-wise unfolding.

### [`P2MW.S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy.ASM21.M2.sc_zero`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Matrix_nonempty_linearEquiv_self_of_natCard_eq_pow_of_natCard_torsionBy.lean#L66-L66) — `flt-anthropic-0957`

Snippet: `samples/flt-anthropic/flt-anthropic-0957.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: smul_zero
- **file**: Mathlib/Algebra/GroupWithZero/Action/Defs.lean
- **derivation**: smul_zero _
- **proof_uses_it**: True
- **explanation**: `sc V c v` is defined as `(algebraMap (ZMod ℓ) (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) c) • v`. Unfolding it, `sc_zero` is `smul_zero` (`a • (0 : V) = 0`) with `a` set to the matrix `algebraMap c`. This is a `SMulZeroClass`/`DistribMulAction` fact, and the current proof is exactly `smul_zero _`. I did not open the Mathlib file to confirm the path above; it is from memory.

### [`P2MW.S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.HerbrandPortM.IsDiscreteValuationRing.residue_aeval_eq`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean#L96-L102) — `flt-anthropic-0958`

Snippet: `samples/flt-anthropic/flt-anthropic-0958.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.map_aeval_eq_aeval_map
- **file**: Mathlib/Algebra/Polynomial/AlgebraMap.lean
- **derivation**: exact map_aeval_eq_aeval_map (ψ := residue B) (φ := residue A) rfl G x
- **explanation**: Mathlib's `map_aeval_eq_aeval_map` states `ψ (aeval a p) = aeval (ψ a) (p.map φ)` for ring homs φ, ψ compatible with the algebra maps, via `h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)`. Taking φ = residue A and ψ = residue B gives the target. The compatibility hypothesis is closed by `rfl`. Mathlib's own `Mathlib/RingTheory/LocalRing/Etale.lean` does exactly this (`map_aeval_eq_aeval_map (ψ := residue S) (φ := residue R) rfl`). The library's proof unfolds `aeval_def` and `eval₂_map` instead and does not call this lemma.

### [`P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.P2mSepKer.isClosedImmersion_one`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale.lean#L29-L33) — `flt-anthropic-0959`

Snippet: `samples/flt-anthropic/flt-anthropic-0959.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.IsClosedImmersion.of_comp
- **file**: Mathlib/AlgebraicGeometry/Morphisms/Separated.lean
- **derivation**: haveI : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f) := by rw [(L.one _).2]; infer_instance
exact IsClosedImmersion.of_comp (L.one (𝟙 (Spec (CommRingCat.of K)))).1 f
- **proof_uses_it**: True
- **explanation**: Mathlib's `IsClosedImmersion.of_comp (f) (g) [IsClosedImmersion (f ≫ g)] [IsSeparated g] : IsClosedImmersion f` says that if f ≫ g is a closed immersion and g is separated, then f is a closed immersion. The theorem is the instance with f := the unit section `(L.one 𝟙).1` and g := the structure map `f`. The hypothesis `IsClosedImmersion (s ≫ f)` holds because `s ≫ f = 𝟙 (Spec K)` by the `.2` field of `SchemeHomOver`. Mathlib has no standalone lemma that a section of a separated morphism is a closed immersion, so the existing proof is already this derivation. It needs one small auxiliary instance, so this is a borderline `special_case`.

### [`P2MW.S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker.R4RRN.mul_apply_10`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_ModularCurve_FullLevel_exists_ratCast_slash_conjElemN_eq_sum_exp_pow_smul_of_mem_Gamma0_of_eq_levelH_inf_ker.lean#L172-L173) — `flt-anthropic-0964`

Snippet: `samples/flt-anthropic/flt-anthropic-0964.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.two_mul_expl
- **file**: Mathlib/Data/Matrix/Mul.lean
- **derivation**: by rw [Matrix.SpecialLinearGroup.coe_mul]; exact (Matrix.two_mul_expl _ _).2.2.1
- **explanation**: Matrix.two_mul_expl states the four entries of a product of 2×2 matrices over a non-unital non-associative semiring. Its third conjunct is (A*B) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0. The target is that same formula for A, B : SL(2, ℤ). To get it, rewrite with SpecialLinearGroup.coe_mul to move the coercion to matrices over ℤ, then apply the third conjunct. The current proof instead uses coe_mul, Matrix.mul_apply and Fin.sum_univ_two. I did not find a Mathlib lemma stated directly for SL(2, ℤ).

### [`P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector.ParchProof.inclArch_mulSingle`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector.lean#L52-L54) — `flt-anthropic-0976`

Snippet: `samples/flt-anthropic/flt-anthropic-0976.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidHom.noncommPiCoprod_mulSingle
- **file**: Mathlib/GroupTheory/NoncommPiCoprod.lean
- **derivation**: MonoidHom.noncommPiCoprod_mulSingle _ w k
- **proof_uses_it**: True
- **explanation**: The library defines `inclArch F := MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F) (fun _ _ hvw => commute_archRowIsometryInclAt₀ F hvw)`. Mathlib's `MonoidHom.noncommPiCoprod_mulSingle` says `noncommPiCoprod ϕ hcomm (Pi.mulSingle i y) = ϕ i y`. Unfolding `inclArch` and taking ϕ := archRowIsometryInclAt₀ F gives the theorem, and the current proof is exactly that application.

### [`P2MW.S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent.NilYoneda.coeff_eq_zero_of_mem_pow`](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent.lean#L331-L333) — `flt-anthropic-0986`

Snippet: `samples/flt-anthropic/flt-anthropic-0986.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: MvPolynomial.mem_pow_idealOfVars_iff'
- **file**: Mathlib/RingTheory/MvPolynomial/Ideal.lean
- **derivation**: (MvPolynomial.mem_pow_idealOfVars_iff' N p).mp hp d hd
- **explanation**: The library's `varIdeal R σ` is an abbrev for `Ideal.span (Set.range MvPolynomial.X)`. That is exactly Mathlib's `MvPolynomial.idealOfVars σ R`. Mathlib's `mem_pow_idealOfVars_iff'` states `p ∈ idealOfVars σ R ^ n ↔ ∀ x, degree x < n → p.coeff x = 0`. The target theorem is its forward direction, applied to `hp`, `d` and `hd`. The library's proof instead uses its own lemma `varIdeal_pow_le_lowVanish`.


## Formal Frontier (45 flagged)

### [`SphereTopology.eastVector_norm`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Circle.lean#L54-L55) — `formal-frontier-0096`

Snippet: `samples/formal-frontier/formal-frontier-0096.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PiLp.norm_single
- **file**: Mathlib/Analysis/Normed/Lp/PiLp.lean
- **derivation**: by rw [eastVector, PiLp.norm_single, norm_one]
- **proof_uses_it**: True
- **explanation**: eastVector is defined as `PiLp.single 2 0 1` in `EuclideanSpace ℝ (Fin 2)`. Mathlib's `PiLp.norm_single` (a simp lemma) says `‖PiLp.single p i b‖ = ‖b‖`. Instantiating it with p = 2, i = 0, b = 1 and then applying `norm_one` gives the result. The current proof is `simp [eastVector]`, which uses this simp lemma. I found no Mathlib lemma about `eastVector` itself.

### [`CategoryTheory.CartesianMonoidalCategory.tensorLeftIsoProd_hom_app_fst`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/SingleCoverGroup.lean#L58-L63) — `formal-frontier-0146`

Snippet: `samples/formal-frontier/formal-frontier-0146.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp
- **file**: Mathlib/CategoryTheory/Limits/IsLimit.lean
- **derivation**: (tensorProductIsBinaryProduct A B).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨.left⟩
- **proof_uses_it**: True
- **explanation**: Mathlib defines `tensorLeftIsoProd` (Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean:800) componentwise as `(tensorProductIsBinaryProduct X Y).conePointUniqueUpToIso (limit.isLimit _)`. The target says the hom component composed with `prod.fst` is `fst A B`. This is `IsLimit.conePointUniqueUpToIso_hom_comp` instantiated at the cone `BinaryFan.mk (fst A B) (snd A B)`, the limit cone of `prod`, and `j = ⟨.left⟩`. The derivation is one line and is the library's own proof. Mathlib has no named lemma for this component statement: a grep for `tensorLeftIsoProd` in Mathlib finds only the definition and one use in `Closed/Cartesian.lean`.

### [`FiniteRegularityFunctions.stalkMap_isLocalHom`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/FiniteRegularityFunctions/Maps.lean#L212-L216) — `formal-frontier-0191`

Snippet: `samples/formal-frontier/formal-frontier-0191.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap
- **file**: Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean
- **derivation**: AlgebraicGeometry.LocallyRingedSpace.isLocalHomStalkMap (locallyRingedSpaceMap IM IN M N r f hf) x
- **explanation**: Mathlib states that for any morphism f of locally ringed spaces and any x, `IsLocalHom (f.stalkMap x).hom`. The target theorem is this statement with f instantiated to the library's own morphism `locallyRingedSpaceMap IM IN M N r f hf`. The current proof uses the structure field `.prop`, which is the same fact, and Mathlib's `isLocalHomStalkMap` is a one-line wrapper around that field (`f.2 x`). I searched LocallyRingedSpace.lean and found this declaration there.

### [`MonoidAlgebra.liftGroupLikeBialgHom_mapDomain_comp`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Bialgebra/MonoidAlgebra.lean#L192-L203) — `formal-frontier-0240`

Snippet: `samples/formal-frontier/formal-frontier-0240.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: MonoidAlgebra.mapDomainBialgHom_comp
- **file**: Mathlib/RingTheory/Bialgebra/MonoidAlgebra.lean
- **derivation**: by rw [mapDomainBialgHom_comp, BialgHom.comp_assoc]
- **explanation**: Mathlib's `mapDomainBialgHom_comp` says `mapDomainBialgHom R (f.comp g) = (mapDomainBialgHom R f).comp (mapDomainBialgHom R g)`. Rewriting the left side of the target with it gives `L.comp ((map f).comp (map α))`. The right side is `(L.comp (map f)).comp (map α)`. The two are equal by `BialgHom.comp_assoc`, which Mathlib has in `Mathlib/RingTheory/Bialgebra/Hom.lean`. The target's `liftGroupLikeBialgHom_mapDomain_*` lemmas play no role in this argument. I did not run it; if `rw` leaves a goal that `comp_assoc` does not close, `rfl` should do it. The current proof goes through `liftGroupLikeBialgHom_mapDomain_eq_iff` and does not use `mapDomainBialgHom_comp`.

### [`QuadraticAlgebra.definingPolynomial_monic`](https://github.com/FormalFrontier/quadratic-algebras/blob/85a6b1bc79989b524a4ecdae6cce17b712a7bd2d/QuadraticAlgebras/AdjoinRoot.lean#L46-L49) — `formal-frontier-0245`

Snippet: `samples/formal-frontier/formal-frontier-0245.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.monic_X_pow_sub
- **file**: Mathlib/Algebra/Polynomial/Monic.lean
- **derivation**: exact monic_X_pow_sub degree_linear_lt
- **proof_uses_it**: True
- **explanation**: `definingPolynomial` is the library's own definition and Mathlib has no declaration of that name. After unfolding, it is `X ^ 2 - (C b * X + C a)`. Mathlib's `Polynomial.monic_X_pow_sub` (`degree p < n → Monic (X ^ n - p)`) gives the result with n = 2 and p = `C b * X + C a`. `degree_linear_lt` supplies the degree hypothesis. The current proof is exactly this one line. I'm calling this a special case rather than a duplicate because the statement is about a library definition. No Mathlib lemma states it directly.

### [`ContinuousCohomology.CorestrictionTransversal.changeRep_rightCoset`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/Corestriction.lean#L168-L174) — `formal-frontier-0260`

Snippet: `samples/formal-frontier/formal-frontier-0260.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.IsComplement.rightCosetEquivalence_equiv_snd
- **file**: Mathlib/GroupTheory/Complement.lean
- **derivation**: exact (rightCosetEquivalence_rel _).symm (S.2.rightCosetEquivalence_equiv_snd (t : G))
- **explanation**: `changeRep T S t` is defined as `(S.2.equiv t).2`, where `S.2 : IsComplement H S`. Mathlib's `rightCosetEquivalence_equiv_snd` (hHT : IsComplement H T) (g : G) says `RightCosetEquivalence H g ((hHT.equiv g).snd : G)`. Taking g := t and flipping the two sides with the symmetry of `RightCosetEquivalence` (`rightCosetEquivalence_rel`, Mathlib/GroupTheory/Coset/Basic.lean) gives the lemma. The target lemma is that statement with the setting specialised to a right transversal and the definition of `changeRep` unfolded. The library's own proof goes through `changeFactor_mul_changeRep` and `rightCoset_eq_iff` instead. I did not check that the derivation elaborates, since I can't run Lean.

### [`Algebra.GrothendieckAddGroup.lift_of`](https://github.com/FormalFrontier/group-theory/blob/2b14628cb53e79783bd51baadcb4fc85667c8da3/GroupTheory/MonoidLocalization/GrothendieckGroup.lean#L43-L46) — `formal-frontier-0274`

Snippet: `samples/formal-frontier/formal-frontier-0274.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: AddSubmonoid.LocalizationMap.lift_eq
- **file**: Mathlib/GroupTheory/MonoidLocalization/Maps.lean
- **derivation**: exact (AddSubmonoid.LocalizationMap.lift_eq (AddSubmonoid.LocalizationMap.addMonoidOf ⊤) (fun _ ↦ AddGroup.isAddUnit _) a)
- **explanation**: Mathlib's GrothendieckGroup.lean has no `lift_of` lemma (only `lift`, `lift_apply`, `lift_symm_apply`). `GrothendieckAddGroup.lift` is defined as `(addMonoidOf ⊤).lift` with `of` being `(addMonoidOf ⊤)`. So `lift_of` is the general localization lemma `Submonoid.LocalizationMap.lift_eq` (additive version), instantiated at the top submonoid, and it holds by definitional unfolding. The library's proof instead uses `symm_apply_apply` of the Equiv. I didn't check the exact argument order of the derivation, so it may need small adjustments.

### [`AlgebraicGeometry.Scheme.Hom.kernImage_mono`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/KernImage.lean#L62-L64) — `formal-frontier-0301`

Snippet: `samples/formal-frontier/formal-frontier-0301.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Set.kernImage_mono
- **file**: Mathlib/Data/Set/Lattice/Image.lean
- **derivation**: fun _ _ h ↦ Set.kernImage_mono h
- **proof_uses_it**: True
- **explanation**: Mathlib has no scheme-level `kernImage`, and grepping `kernImage` in Mathlib/AlgebraicGeometry found nothing. The theorem's `Scheme.Hom.kernImage` is the library's own definition. It is `Set.kernImage π` on the underlying sets, packaged as an open set. The order on `Opens` is inclusion of the underlying sets. Monotonicity is therefore `Set.kernImage_mono : Monotone (kernImage f)` (Data/Set/Lattice/Image.lean:65) applied to the underlying sets, after unfolding the definition. That is the current one-line proof, so this is a thin lift of Mathlib's lemma. It is not an exact duplicate, because the statement is about a different function on `Opens`.

### [`SignProduct.flip_apply_self`](https://github.com/FormalFrontier/continuous-group-cohomology/blob/65345921370bfc91ac84c049ba172360704e8bab/ContinuousGroupCohomology/DiscreteProduct.lean#L98-L99) — `formal-frontier-0324`

Snippet: `samples/formal-frontier/formal-frontier-0324.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Function.update_self
- **file**: Mathlib/Logic/Function/Basic.lean
- **derivation**: Function.update_self index (-1) 1
- **proof_uses_it**: True
- **explanation**: `flip index` is defined as `Function.update (1 : SignGroup) index (-1)`. The statement `flip index index = -1` therefore unfolds to `update 1 index (-1) index = -1`. That is `Function.update_self index (-1) 1`, which states `update f a v a = v`. The current proof uses it indirectly: `simp [flip]` rewrites with the simp lemma `Function.update_self`. I only read `update_self` and the definition. I did not check whether `SignGroup` unfolds to a Pi type with the `1` and `-1` shapes needed, so the `exact` form may need `show` or `unfold flip`.

### [`Subcoalgebra.smul_mem`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra.lean#L234-L235) — `formal-frontier-0325`

Snippet: `samples/formal-frontier/formal-frontier-0325.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SMulMemClass.smul_mem
- **file**: Mathlib/GroupTheory/GroupAction/SubMulAction.lean
- **derivation**: SMulMemClass.smul_mem r hx
- **explanation**: Mathlib has no Subcoalgebra. The library gives `Subcoalgebra K C` an instance `SMulMemClass (Subcoalgebra K C) K C` (line 108 of the same file). It is proved directly from `Submodule.smul_mem`, not from the theorem being judged. Mathlib's `SMulMemClass.smul_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r • m ∈ s` is then this statement with S := Subcoalgebra K C. The theorem's own proof uses `Submodule.smul_mem` on `D.toSubmodule` instead. I count this as a special case rather than an exact duplicate because the match is a generic class lemma instantiated at the library's own type.

### [`RingedSpaces.Modules.RingedSpacePullback.nativeComparison_counit`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/RingedSpacePullback.lean#L195-L200) — `formal-frontier-0326`

Snippet: `samples/formal-frontier/formal-frontier-0326.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit
- **file**: Mathlib/CategoryTheory/Adjunction/Unique.lean
- **derivation**: Adjunction.leftAdjointUniq_hom_app_counit (adjunction f) (nativeAdjunction f) N
- **proof_uses_it**: True
- **explanation**: nativeComparison f is defined as (adjunction f).leftAdjointUniq (nativeAdjunction f). The theorem is Mathlib's general lemma leftAdjointUniq_hom_app_counit, with the two adjunctions for the ringed-space pullback/pushforward plugged in. The statement matches the Mathlib one up to unfolding the definition of nativeComparison. The library's proof is a direct application of that lemma.

### [`SpecialLinearCoordinateRing.quotient_det`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/SpecialLinearCoordinateRing.lean#L59-L63) — `formal-frontier-0337`

Snippet: `samples/formal-frontier/formal-frontier-0337.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.mk_eq_one_iff_sub_mem
- **file**: Mathlib/RingTheory/Ideal/Quotient/Defs.lean
- **derivation**: exact (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.mem_span_singleton_self _)
- **explanation**: Mathlib has `Ideal.Quotient.mk_eq_one_iff_sub_mem (x : R) : mk I x = 1 ↔ x - 1 ∈ I`. The theorem is the case I = span {det - 1}, x = det, where `quotient K n` is `Ideal.Quotient.mkₐ`, which is defeq to `Ideal.Quotient.mk` on elements. The membership `det - 1 ∈ span {det - 1}` is `Ideal.mem_span_singleton_self`. The current proof does the same thing by hand: it shows that `mk (det - 1) = 0` and then uses `map_sub`, `map_one` and `sub_eq_zero`. I found nothing about the library's own `SpecialLinearCoordinateRing` or `GeneralLinearCoordinateRing` definitions in Mathlib.

### [`AlgebraicGeometry.unitriangularStageCoordinateMap_π`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/UnitriangularStageCoordinates.lean#L77-L83) — `formal-frontier-0366`

Snippet: `samples/formal-frontier/formal-frontier-0366.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.Pi.lift_π
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Products.lean
- **derivation**: Limits.Pi.lift_π _ ij
- **proof_uses_it**: True
- **explanation**: unitriangularStageCoordinateMap is by definition Limits.Pi.lift of the family of coordinate projections. The statement is exactly Pi.lift_π (lift p ≫ π f b = p b) with p := unitriangularStageCoordinateProjection K n r hr, after unfolding the definition. The current proof is `simp [unitriangularStageCoordinateMap]`, which uses the simp-tagged Pi.lift_π.

### [`CategoryTheory.MorphismProperty.Over.pullbackPairingSymmetry_hom_app_fst`](https://github.com/FormalFrontier/morphism-properties/blob/3c50b1e5fea23c3a119c5eb9157c3a1ba7f3b8bc/MorphismProperties/PullbackPairing.lean#L365-L373) — `formal-frontier-0372`

Snippet: `samples/formal-frontier/formal-frontier-0372.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst
- **file**: Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean
- **derivation**: by rw [pullbackPairingSymmetry_hom_app_left]; exact pullbackSymmetry_hom_comp_fst A.hom B.hom
- **proof_uses_it**: True
- **explanation**: The library lemma `pullbackPairingSymmetry_hom_app_left` is proved by `rfl`. It says that `((pullbackPairingSymmetry E Q P S).hom.app (A, B)).left` is `(pullbackSymmetry A.hom B.hom).hom`. After that unfolding, the goal is exactly Mathlib's `pullbackSymmetry_hom_comp_fst f g : (pullbackSymmetry f g).hom ≫ pullback.fst g f = pullback.snd f g`, with `f := A.hom` and `g := B.hom`. The theorem is therefore that Mathlib lemma, restated for the library's own symmetry morphism on `Over` objects. The `HasPullback` instance is `hasPullback_symmetry`, as in Mathlib's statement. The current proof already uses the Mathlib lemma.

### [`Profinite.indDualRealizationPresentationIso_refl`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/IndDualRealization.lean#L629-L636) — `formal-frontier-0389`

Snippet: `samples/formal-frontier/formal-frontier-0389.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Iso.symm_self_id
- **file**: Mathlib/CategoryTheory/Iso.lean
- **derivation**: exact (indDualRealizationComparisonOfIso X e c hc).symm_self_id
- **proof_uses_it**: True
- **explanation**: `indDualRealizationPresentationIso X e c hc Y e' d hd` is defined as `(indDualRealizationComparisonOfIso X e c hc).symm ≪≫ indDualRealizationComparisonOfIso Y e' d hd`. With Y = X, e' = e, d = c and hd = hc, it becomes `α.symm ≪≫ α` for α = `indDualRealizationComparisonOfIso X e c hc : Q-realization ≅ c.pt`. Mathlib's `Iso.symm_self_id (α : X ≅ Y) : α.symm ≪≫ α = Iso.refl Y` gives `Iso.refl c.pt`, which is the claim. The library's proof is exactly this one-line application after unfolding the definition. The remaining content is the library's own definition, so I judged this a special case rather than a duplicate. I found no Mathlib lemma about the library-specific iso itself.

### [`ToricIdeals.RationalNormalCurve.minor_mem`](https://github.com/FormalFrontier/toric-ideals/blob/b91a7be3aab7ee857dfe6d3c0450f0a2af454027/ToricIdeals/RationalNormalCurve.lean#L181-L185) — `formal-frontier-0437`

Snippet: `samples/formal-frontier/formal-frontier-0437.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: Ideal.mem_span_range_self
- **file**: Mathlib/RingTheory/Ideal/Span.lean
- **derivation**: exact Ideal.mem_span_range_self
- **explanation**: hankelIdeal k n is by definition Ideal.span (Set.range (hankelMinor k n)). The theorem says hankelMinor k n p lies in that span. Ideal.mem_span_range_self states `f x ∈ span (range f)` for any f and x. The statements are the same after unfolding hankelIdeal. The current proof reaches the same fact through Ideal.subset_span and Set.mem_range_self.

### [`ToricIdeals.RationalNormalCurve.mem_quotientHomogeneousSubmodule_iff`](https://github.com/FormalFrontier/toric-ideals/blob/b91a7be3aab7ee857dfe6d3c0450f0a2af454027/ToricIdeals/RationalNormalCurve/HomogeneousBasis.lean#L99-L104) — `formal-frontier-0440`

Snippet: `samples/formal-frontier/formal-frontier-0440.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.mem_map
- **file**: Mathlib/Algebra/Module/Submodule/Map.lean
- **derivation**: Submodule.mem_map
- **proof_uses_it**: True
- **explanation**: The theorem is the membership criterion for a pushforward submodule, `Submodule.mem_map : x ∈ p.map f ↔ ∃ y, y ∈ p ∧ f y = x`. The library's `quotientHomogeneousSubmodule` is an `abbrev` for `(homogeneousSubmodule (Fin (n+1)) R d).map (Ideal.Quotient.mkₐ R (hankelIdeal R n)).toLinearMap`. Here `y ∈ homogeneousSubmodule _ R d` unfolds definitionally to `y.IsHomogeneous d`. The current proof is exactly `Submodule.mem_map`. I did not open the Mathlib file to confirm the path above, and I did not search for other candidates.

### [`UnitriangularCoordinateRing.polynomialQuotientToCoordinateRing_comp_polynomialQuotient`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/UnitriangularCoordinateRing.lean#L367-L370) — `formal-frontier-0452`

Snippet: `samples/formal-frontier/formal-frontier-0452.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.liftₐ_comp
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: Ideal.Quotient.liftₐ_comp _ _ _
- **proof_uses_it**: True
- **explanation**: Mathlib's `Ideal.Quotient.liftₐ_comp` says `(liftₐ I f hI).comp (mkₐ R I) = f`. In the library, `polynomialQuotientToCoordinateRing` is defined as `Ideal.Quotient.liftₐ (polynomialIdeal K ι) (polynomialToCoordinateRing K ι) _`. `polynomialQuotient` is the quotient map `mkₐ`. This is my reading of the definitions, and I did not open the definition of `polynomialQuotient` itself. The theorem is therefore `liftₐ_comp` with `I`, `f` and `hI` fixed to the library's specific ideal and map, and the current proof is exactly `Ideal.Quotient.liftₐ_comp _ _ _`.

### [`Coalgebra.RightComodule.Subcomodule.coaction_mem_range_iff`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/RightComodule.lean#L472-L475) — `formal-frontier-0496`

Snippet: `samples/formal-frontier/formal-frontier-0496.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.mem_range
- **file**: Mathlib/Algebra/Module/Submodule/Range.lean
- **derivation**: LinearMap.mem_range
- **explanation**: The theorem is `x ∈ range f ↔ ∃ y, f y = x` for f = U.toSubmodule.subtype.rTensor C and x = X.coaction m. This is LinearMap.mem_range with f and x instantiated. The current proof is `Iff.rfl`, which is also how Mathlib proves it. In Mathlib, `mem_range` takes `[RingHomSurjective τ₁₂]`, and this holds for the identity ring hom.

### [`SSet.homologyZeroPoint_homology₀Iso`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Reduced.lean#L105-L111) — `formal-frontier-0509`

Snippet: `samples/formal-frontier/formal-frontier-0509.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom
- **file**: Mathlib/AlgebraicTopology/SimplicialSet/Homology/HomologyZero.lean
- **derivation**: by dsimp only [homologyZeroPoint]; simpa only [Category.assoc] using SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom X R x
- **proof_uses_it**: True
- **explanation**: The library defines homologyZeroPoint X R x as liftCycles (X.ιChainComplex x) 0 _ _ ≫ homologyπ 0. Unfolding it, the target statement is exactly Mathlib's lemma liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom, up to reassociation: liftCycles ≫ homologyπ ≫ (homology₀Iso).hom = Sigma.ι _ (π₀.mk x). The current proof is this unfolding followed by that lemma. I found no Mathlib declaration named homologyZeroPoint.

### [`RingedSpaces.Modules.SheafInverseImage.ringIso_inv_hom_apply`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/SheafInverseImageHom.lean#L126-L135) — `formal-frontier-0515`

Snippet: `samples/formal-frontier/formal-frontier-0515.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Iso.inv_hom_id_app_apply
- **file**: Mathlib/CategoryTheory/Types/Basic.lean
- **derivation**: exact Iso.inv_hom_id_app_apply ((sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{v}).mapIso (ringIso f S)) V elem
- **explanation**: The theorem is the elementwise form of `Iso.inv_hom_id_app` for the iso of presheaves of rings obtained by applying `sheafToPresheaf` to `ringIso f S`. It states `e.hom.app V (e.inv.app V x) = x` for a natural isomorphism `e` into a concrete category (`RingCat`). The apply-version `Iso.inv_hom_id_app_apply` is generated by `attribute [elementwise (attr := simp)] Iso.hom_inv_id_app Iso.inv_hom_id_app` in Types/Basic.lean. `Iso.inv_hom_id_app` itself is in NatIso.lean and holds for general `F G : C ⥤ D`. The library's proof builds the same `e` and uses the non-elementwise `Iso.inv_hom_id_app` plus `congrArg`. I couldn't confirm the elementwise lemma's exact generated signature, since it is produced by attribute rather than declared in source.

### [`Matrix.isIdempotentElem_single_one`](https://github.com/FormalFrontier/general-linear-groups/blob/ff8095ef752bcc8bacb5b7b18255fc88470e5e97/GeneralLinearGroups/MatrixCorner.lean#L27-L30) — `formal-frontier-0597`

Snippet: `samples/formal-frontier/formal-frontier-0597.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Matrix.single_mul_single_same
- **file**: Mathlib/Data/Matrix/Basis.lean
- **derivation**: by simpa [IsIdempotentElem] using Matrix.single_mul_single_same (c := (1 : R)) i i i (1 : R)
- **proof_uses_it**: True
- **explanation**: IsIdempotentElem x unfolds to x * x = x. Mathlib's single_mul_single_same states single i j c * single j k d = single i k (c * d). With j = k = i and c = d = 1, this gives single i i 1 * single i i 1 = single i i (1 * 1), and 1 * 1 = 1 by simp. The current proof's `simp [IsIdempotentElem]` uses this lemma, which is tagged @[simp]. I found no Mathlib lemma that states idempotency of the matrix unit directly. I searched Mathlib/Data/Matrix for IsIdempotentElem and found nothing, and the other IsIdempotentElem matches are about Pi.single.

### [`CategoryTheory.pullback_eq_inf_of_isPullback`](https://github.com/FormalFrontier/spectral-stone-duality/blob/78b803577679fc37120fa3406833af653fe12018/SpectralStoneDuality/CategoryTheory/Lattice/Extensive.lean#L57-L60) — `formal-frontier-0615`

Snippet: `samples/formal-frontier/formal-frontier-0615.lean`

- **verdict**: `duplicate`
- **mathlib_declaration**: CategoryTheory.Limits.CompleteLattice.pullback_eq_inf
- **file**: Mathlib/CategoryTheory/Limits/Lattice.lean
- **derivation**: CategoryTheory.Limits.CompleteLattice.pullback_eq_inf f g
- **explanation**: Mathlib's `CompleteLattice.pullback_eq_inf` has the same hypotheses (`SemilatticeInf α`, `OrderTop α`, `α : Type u`, `f : x ⟶ z`, `g : y ⟶ z`) and the same conclusion `pullback f g = x ⊓ y`. The library's own docstring says its statement "agrees with Mathlib's chosen pullback", so the library's lemma restates Mathlib's. The library proves it another way, using its own `isPullback_inf`.

### [`ProfiniteGrp.closedNormalQuotientProj_isQuotientMap`](https://github.com/FormalFrontier/profinite-groups/blob/d21abb3f7fedd7241f3dbcb91ba8eed73d2caf9c/ProfiniteGroups/ClosedQuotient.lean#L101-L105) — `formal-frontier-0617`

Snippet: `samples/formal-frontier/formal-frontier-0617.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: QuotientGroup.isQuotientMap_mk
- **file**: Mathlib/Topology/Algebra/Group/Quotient.lean
- **derivation**: QuotientGroup.isQuotientMap_mk N.toSubgroup
- **proof_uses_it**: True
- **explanation**: Mathlib's `QuotientGroup.isQuotientMap_mk (N : Subgroup G) : IsQuotientMap (mk : G → G ⧸ N)` says the quotient map from a topological group to its quotient by a subgroup is a quotient map. The library's `closedNormalQuotientProj` is, by `closedNormalQuotientProj_apply` (which is `rfl`), the map `g ↦ QuotientGroup.mk g` wrapped as a morphism of `ProfiniteGrp`. The theorem is therefore Mathlib's lemma applied to `N.toSubgroup`, and the current proof is exactly that one-line application.

### [`ValuationSubring.ofPrime_compositeIdeal`](https://github.com/FormalFrontier/adic-modules/blob/6f6fa8b3b08a9dba6faa90e328c8d528645f7d5b/AdicModules/CompositeValuationSubring.lean#L168-L174) — `formal-frontier-0665`

Snippet: `samples/formal-frontier/formal-frontier-0665.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ValuationSubring.ofPrime_idealOfLE
- **file**: Mathlib/RingTheory/Valuation/ValuationSubring.lean
- **derivation**: (A.composite W).ofPrime_idealOfLE A (A.composite_le W)
- **proof_uses_it**: True
- **explanation**: Mathlib's `ValuationSubring.ofPrime_idealOfLE (R S) (h : R ≤ S) : ofPrime R (idealOfLE R S h) = S` is stated for arbitrary valuation subrings R ≤ S of K. In this library `compositeIdeal A W` is defined as `(A.composite W).idealOfLE A (A.composite_le W)`. Taking R := A.composite W and S := A gives the target statement by unfolding that definition. The library's proof already does exactly this. Mathlib has no `composite` or `compositeIdeal` of its own (searched, no matches), so the only matching content is this general lemma.

### [`AlgebraicGeometry.specialLinearModuleMatrixEquiv_entry`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/SpecialLinearModule.lean#L139-L148) — `formal-frontier-0669`

Snippet: `samples/formal-frontier/formal-frontier-0669.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: LinearMap.toMatrix_apply
- **file**: Mathlib/LinearAlgebra/Matrix/ToLin.lean
- **derivation**: exact LinearMap.toMatrix_apply _ _ _ _ _  -- the SL matrix is defeq to LinearMap.toMatrix b b f (Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq is rfl)
- **proof_uses_it**: True
- **explanation**: The library defines specialLinearModuleMatrixEquiv as (Matrix.SpecialLinearGroup.toLin_equiv b).symm. Mathlib's `Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq` (Mathlib/LinearAlgebra/SpecialLinearGroup.lean, proved by rfl) says that this matrix is `LinearMap.toMatrix b b f`. `LinearMap.toMatrix_apply` then gives the entry `b.repr (f (b j)) i`. The theorem is that statement with b := generalLinearScalarBasis K V indexType basis R, and its current proof already uses these two lemmas. I found no single Mathlib lemma that states the SL entry formula directly, so the match is through toMatrix_apply plus the rfl lemma. That is why I chose special_case over duplicate.

### [`Subcoalgebra.coe_smul`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra.lean#L266-L268) — `formal-frontier-0685`

Snippet: `samples/formal-frontier/formal-frontier-0685.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SMulMemClass.val_smul
- **file**: Mathlib/GroupTheory/GroupAction/SubMulAction.lean
- **derivation**: SMulMemClass.val_smul D r x
- **explanation**: The library gives `Subcoalgebra K C` a `SetLike` structure and an `SMulMemClass (Subcoalgebra K C) K C` instance. Mathlib's `SMulMemClass.val_smul (s : S) (r : R) (x : s) : ((r • x : s) : M) = r • (x : M)` is a simp/norm_cast lemma. It holds for any `SetLike S M` with `SMulMemClass S R M`, and the library's lemma is the instance `S := Subcoalgebra K C`, `R := K`, `M := C`. The `SMul K D` in the library's statement comes from `Module K D`, which is `D.toSubmodule.module`. That is defeq to the generic `SMulMemClass.smul` instance, so the instantiation should typecheck by unification, but I could not run Lean to confirm it. The current proof is `rfl`, not this lemma. `Submodule.coe_smul` is a similar match for `Submodule`.

### [`AlgebraicGeometry.unitriangularStageFromGL_comp_quotient`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/GroupScheme/UnitriangularStages.lean#L148-L152) — `formal-frontier-0692`

Snippet: `samples/formal-frontier/formal-frontier-0692.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.liftₐ_comp
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: Ideal.Quotient.liftₐ_comp _ _ _
- **proof_uses_it**: True
- **explanation**: unitriangularStageFromGL is defined as Ideal.Quotient.liftₐ (ideal K n r) (unitriangularFromGL K (Fin n) R s.1) _, and quotient K n r is the quotient map by that ideal. The theorem is therefore Mathlib's `(Ideal.Quotient.liftₐ I f hI).comp (Ideal.Quotient.mkₐ R₁ I) = f` with I, f and hI instantiated. The library's proof is exactly `Ideal.Quotient.liftₐ_comp _ _ _`.

### [`Subcoalgebra.coe_mem`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra.lean#L243-L244) — `formal-frontier-0700`

Snippet: `samples/formal-frontier/formal-frontier-0700.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: SetLike.coe_mem
- **file**: Mathlib/Data/SetLike/Basic.lean
- **derivation**: theorem coe_mem (x : D) : (x : C) ∈ D := SetLike.coe_mem x
- **explanation**: Subcoalgebra K C has a SetLike instance (line 57 of the library file), and the theorem is SetLike.coe_mem, which states (x : p) → (x : B) ∈ p, instantiated at the library's own SetLike structure. The current proof uses x.property directly instead. Mathlib has no Subcoalgebra declarations.

### [`Subcoalgebra.map_le_iff`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/Coalgebra/Subcoalgebra/Map.lean#L121-L130) — `formal-frontier-0724`

Snippet: `samples/formal-frontier/formal-frontier-0724.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Submodule.map_le_iff_le_comap
- **file**: Mathlib/Algebra/Module/Submodule/Map.lean
- **derivation**: by rw [map_toSubmodule]; exact Submodule.map_le_iff_le_comap
- **explanation**: Mathlib has no Subcoalgebra declarations, so none matches directly. The underlying submodule of `map f D` is `Submodule.map f.toLinearMap D.toSubmodule` (`map_toSubmodule`, proved by `rfl`). `Submodule.map_le_iff_le_comap` says `map f p ≤ q ↔ p ≤ comap f q`. Unfolding `≤` and `comap`, the right side is `∀ x ∈ D.toSubmodule, f x ∈ S`, which is definitionally the theorem's right side. I did not open `Submodule.map_le_iff_le_comap` to check its statement. I also did not check that the `exact` step closes by defeq. `Set.image_subset_iff` is the set-level analogue.

### [`RingedSpaces.Modules.RingedSpacePushforward.restrictPushforwardIso_inverseLaws`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/RingedSpacePushforward.lean#L166-L173) — `formal-frontier-0725`

Snippet: `samples/formal-frontier/formal-frontier-0725.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Iso.hom_inv_id_app
- **file**: Mathlib/CategoryTheory/NatIso.lean
- **derivation**: ⟨(restrictPushforwardIso f).hom_inv_id_app M, (restrictPushforwardIso f).inv_hom_id_app M⟩
- **proof_uses_it**: True
- **explanation**: The theorem is the conjunction of the two standard laws for a natural isomorphism, applied to `restrictPushforwardIso f` at the object `M`. The first conjunct is `Iso.hom_inv_id_app` and the second is `Iso.inv_hom_id_app`. Both are in Mathlib/CategoryTheory/NatIso.lean (lines 59 and 63), and the library's proof is exactly this one-line pairing. The match is not a single declaration: Mathlib has the two laws as separate lemmas, and I did not find a lemma stating their conjunction. I judged a one-line pairing of two instantiated lemmas to be a special case. If the criteria require a single declaration, the answer would be `none_found`.

### [`AlgebraicGeometry.sourceOrderTensor_smul_tmul`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/MatrixEndBaseChange.lean#L58-L62) — `formal-frontier-0727`

Snippet: `samples/formal-frontier/formal-frontier-0727.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: TensorProduct.smul_tmul'
- **file**: Mathlib/LinearAlgebra/TensorProduct/Defs.lean
- **derivation**: by simpa [sourceOrderTensorEquiv] using TensorProduct.smul_tmul' r s v
- **proof_uses_it**: True
- **explanation**: Unfolding sourceOrderTensorEquiv (which is TensorProduct.comm) turns the statement into r • (s ⊗ₜ v) = (r * s) ⊗ₜ v in R ⊗[K] V. That is TensorProduct.smul_tmul' (r • m ⊗ₜ n = (r • m) ⊗ₜ n) with m = s and n = v. Since r • s = r * s for smul_eq_mul, the equality follows. The library's proof is `simp [sourceOrderTensorEquiv, TensorProduct.smul_tmul']`, which already uses this lemma.

### [`RingedSpaces.Modules.tensorSectionHomEquiv_apply`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/PresheafChangeOfRings.lean#L77-L83) — `formal-frontier-0738`

Snippet: `samples/formal-frontier/formal-frontier-0738.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: ModuleCat.extendRestrictScalarsAdj_homEquiv_apply
- **file**: Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean
- **derivation**: letI : CommRing ((ringPresheaf A).obj U) := inferInstanceAs (CommRing (A.obj U))
letI : CommRing ((ringPresheaf B).obj U) := inferInstanceAs (CommRing (B.obj U))
exact ModuleCat.extendRestrictScalarsAdj_homEquiv_apply t m
- **proof_uses_it**: True
- **explanation**: The library's tensorSectionHomEquiv is defined as (ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _ with f = ((ringMap A B theta).app U).hom. tensorUnitSection is the unit of the same adjunction at M.obj U. Mathlib's lemma says homEquiv φ m = φ (1 ⊗ₜ m) for the extension/restriction of scalars adjunction. That is the theorem, with the specific ring map and sections instantiated. The two are related by unfolding the library's definitions. The unit applied to m is defeq to 1 ⊗ₜ m. The current proof is just that lemma plus two `let` instance declarations. The `let`s only supply the CommRing instances on the ring presheaf values, so I count the derivation as routine glue.

### [`RingedSpaces.Modules.SheafInverseImage.pointwiseToPullbackFac`](https://github.com/FormalFrontier/ringed-spaces/blob/f5e2fa019c2b1904b41efae2f5bf20e17ff28871/RingedSpaces/Modules/SheafInverseImage.lean#L239-L253) — `formal-frontier-0740`

Snippet: `samples/formal-frontier/formal-frontier-0740.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: CategoryTheory.Functor.descOfIsLeftKanExtension_fac
- **file**: Mathlib/CategoryTheory/Functor/KanExtension/Basic.lean
- **derivation**: by simpa only [PresheafInverseImage.pointwiseToPullback, Functor.leftKanExtensionUnique, Functor.leftKanExtensionUniqueOfIso, Iso.refl_hom, Category.id_comp] using Functor.descOfIsLeftKanExtension_fac (α := (Opens.map f).op.pointwiseLeftKanExtensionUnit P) (G := (Opens.map f).op.leftKanExtension P) (β := (Opens.map f).op.leftKanExtensionUnit P)
- **proof_uses_it**: True
- **explanation**: The theorem says the comparison iso pointwiseToPullback, defined as Mathlib's `Functor.leftKanExtensionUnique` between the pointwise left Kan extension and the chosen one, is compatible with the two units. Unfolding `leftKanExtensionUnique`/`leftKanExtensionUniqueOfIso` (with `Iso.refl`) gives hom = `descOfIsLeftKanExtension _ α G (𝟙 ≫ β)`. The statement is then exactly `Functor.descOfIsLeftKanExtension_fac` with L = (Opens.map f).op, F = P, α the pointwise unit and β the `leftKanExtensionUnit`. I found no Mathlib lemma stating this directly for `leftKanExtensionUnique` (grep over Mathlib for lemmas named `leftKanExtensionUnique*`). The existing proof is already this one-declaration derivation, with unfolding and `simpa`.

### [`Subgroup.RightTransversal.changeFactor_mul_changeRep`](https://github.com/FormalFrontier/group-theory/blob/2b14628cb53e79783bd51baadcb4fc85667c8da3/GroupTheory/Transversal.lean#L115-L117) — `formal-frontier-0825`

Snippet: `samples/formal-frontier/formal-frontier-0825.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subgroup.IsComplement.equiv_fst_mul_equiv_snd
- **file**: Mathlib/GroupTheory/Complement.lean
- **derivation**: S.2.equiv_fst_mul_equiv_snd _
- **proof_uses_it**: True
- **explanation**: The library defines changeFactor T S t := (S.2.equiv t).1 and changeRep T S t := (S.2.equiv t).2. After unfolding these, the statement is exactly Mathlib's `IsComplement.equiv_fst_mul_equiv_snd`, which says ↑(hST.equiv g).fst * (hST.equiv g).snd = g. It is applied to S.2 and g = ↑t. No Mathlib declaration mentions changeFactor or changeRep, so the match is the underlying lemma, and the current proof is already that one-line application. The one caveat is that the content could be read as sitting in the library's own definitions, which would make this none_found. I judged that the content is Mathlib's lemma.

### [`TopModuleCat.algebraMap_mulAction_eq_smul`](https://github.com/FormalFrontier/algebraic-direct-limits/blob/1bf0740b01951905e0ba12bd5d2bdb67819c12d1/AlgebraicDirectLimits/Topology/Restriction.lean#L393-L400) — `formal-frontier-0840`

Snippet: `samples/formal-frontier/formal-frontier-0840.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Algebra.smul_def
- **file**: Mathlib/Algebra/Algebra/Defs.lean
- **derivation**: funext fun p => (Algebra.smul_def p.1 p.2).symm
- **proof_uses_it**: True
- **explanation**: Algebra.smul_def says r • x = algebraMap R A r * x. The target is the function-extensional form of this on pairs (R × S), obtained by funext and symm. The library's proof already does exactly that. I found no Mathlib lemma stating the function-level equality directly.

### [`UnitriangularStageCoordinateRing.survivingInclusion_injective`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/UnitriangularStagePolynomial.lean#L49-L50) — `formal-frontier-0862`

Snippet: `samples/formal-frontier/formal-frontier-0862.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Subtype.val_injective
- **file**: Mathlib/Data/Subtype.lean
- **derivation**: Subtype.val_injective
- **proof_uses_it**: True
- **explanation**: survivingInclusion n r is defined as Subtype.val on the subtype SurvivingPair n r. The theorem is therefore Subtype.val_injective with the predicate fixed, after unfolding the definition. I did not open the Mathlib file to confirm the path. The library's proof is already exactly `Subtype.val_injective`.

### [`ToricIdeals.RationalNormalCurve.quotientHomogeneousCoordinates_ext`](https://github.com/FormalFrontier/toric-ideals/blob/b91a7be3aab7ee857dfe6d3c0450f0a2af454027/ToricIdeals/RationalNormalCurve/HomogeneousBasis.lean#L570-L575) — `formal-frontier-0881`

Snippet: `samples/formal-frontier/formal-frontier-0881.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Module.Basis.ext_elem
- **file**: Mathlib/LinearAlgebra/Basis/Defs.lean
- **derivation**: (quotientHomogeneousBasis R n d).ext_elem h
- **explanation**: Mathlib has `Module.Basis.ext_elem` (alias of `ext_elem_iff`): `(∀ i, b.repr x i = b.repr y i) → x = y`. The library's coordinates `quotientHomogeneousCoordinates R n d x i` are defined as `(quotientHomogeneousBasis R n d).equivFun x i`, which is `repr x i` by rfl (see `quotientHomogeneousCoordinates_apply`). So `h` has the required form up to defeq, and the theorem is this lemma instantiated at the library's basis. The library's current proof uses `LinearEquiv.injective` and `funext` instead.

### [`DirectLimit.VaryingScalar.of_map`](https://github.com/FormalFrontier/algebraic-direct-limits/blob/1bf0740b01951905e0ba12bd5d2bdb67819c12d1/AlgebraicDirectLimits/VaryingScalar.lean#L127-L129) — `formal-frontier-0897`

Snippet: `samples/formal-frontier/formal-frontier-0897.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: DirectLimit.mk_apply
- **file**: Mathlib/Order/DirectedInverseSystem.lean
- **derivation**: DirectLimit.mk_apply i j m hij  -- (of_apply is rfl; or `by simpa using DirectLimit.mk_apply i j m hij`)
- **explanation**: The target says `of … j (g i j hij m) = of … i m`. By `of_apply` (which is `rfl`), `of … i m` is `⟦⟨i, m⟩⟧` in `DirectLimit M g`. So the goal is `⟦⟨j, g i j hij m⟩⟧ = ⟦⟨i, m⟩⟧`. That is exactly Mathlib's `DirectLimit.mk_apply (i j : ι) (x : F i) (h : i ≤ j) : ⟦⟨j, f _ _ h x⟩⟧ = ⟦⟨i, x⟩⟧`, instantiated with `F := M` and `f := g · · ·`. The library's proof uses `DirectLimit.eq_of_le`, which `mk_apply` itself is proved from, so `mk_apply` is the same fact with the sides already oriented correctly. The Mathlib `Module.DirectLimit.of_f` and `Ring.of_f` lemmas are about a different `of`, so they do not apply. The varying-scalar `of` is the library's own definition. I did not run this derivation in Lean. The coercion of `g i j hij` to a function may need a `simpa` or a change of form.

### [`ModuleCat.piRightSingle_add`](https://github.com/FormalFrontier/projective-modules/blob/630c227210958554603cb3f949c6522133d38af3/ProjectiveModules/Module/RightProduct.lean#L478-L482) — `formal-frontier-0906`

Snippet: `samples/formal-frontier/formal-frontier-0906.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Pi.single_add
- **file**: Mathlib/Algebra/Group/Pi/Lemmas.lean
- **derivation**: by classical exact Pi.single_add (f := fun j => (Mi j : Type uM)) i x y
- **proof_uses_it**: True
- **explanation**: `piRightSingle Ri Mi i x` is defined as `Pi.single i x` on the family `fun i => Mi i`, with `Classical.decEq` as the decidability instance. The theorem is therefore `Pi.single_add`, the additive form of `Pi.mulSingle_mul`, with `f := fun j => (Mi j : Type uM)`. It needs only unfolding `piRightSingle` and `classical`. The library's proof already does this. I checked the statement of `Pi.mulSingle_mul` at Lemmas.lean:300, but did not look at the generated `Pi.single_add` itself.

### [`SphereTopology.sphere2NorthVector_norm`](https://github.com/FormalFrontier/sphere-topology/blob/19128260805ce0101608760b6cd04dfb5140d697/SphereTopology/Homology/Singular/Sphere.lean#L55-L56) — `formal-frontier-0912`

Snippet: `samples/formal-frontier/formal-frontier-0912.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PiLp.norm_single
- **file**: Mathlib/Analysis/Normed/Lp/PiLp.lean
- **derivation**: by rw [sphere2NorthVector, PiLp.norm_single, norm_one]
- **proof_uses_it**: True
- **explanation**: `sphere2NorthVector` is defined as `PiLp.single 2 2 1` in `EuclideanSpace ℝ (Fin 3)`. `PiLp.norm_single` says `‖single p i b‖ = ‖b‖`. Instantiating it at p = 2, i = 2, b = 1 and then using `norm_one` gives `‖sphere2NorthVector‖ = 1`. The current proof is `simp [sphere2NorthVector]`, which uses this `@[simp]` lemma. I did not look for a Mathlib lemma about this exact vector.

### [`AlgebraicGeometry.powerRootAlgebra_free`](https://github.com/FormalFrontier/scheme-properties/blob/3455b4b9192b77c1754729bafa64f99ea8c5c838/SchemeProperties/PowerImage.lean#L119-L123) — `formal-frontier-0921`

Snippet: `samples/formal-frontier/formal-frontier-0921.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Polynomial.Monic.free_adjoinRoot
- **file**: Mathlib/RingTheory/AdjoinRoot.lean
- **derivation**: exact (Polynomial.monic_X_pow_sub_C (a : A.obj) (Nat.ne_of_gt hn)).free_adjoinRoot
- **proof_uses_it**: True
- **explanation**: Mathlib's `Polynomial.Monic.free_adjoinRoot` says that for monic g over R, AdjoinRoot g is a free R-module. The theorem is the instance g = X^n - C a, which is `powerRootPolynomial K n A a` by definition. It is monic for n ≠ 0 by `Polynomial.monic_X_pow_sub_C`. The current proof is exactly this one-line application.

### [`SpecialLinearCoordinateRing.coordinateRingToPolynomialQuotient_comp_quotient`](https://github.com/FormalFrontier/algebraic-groups/blob/1e9a9adc519130a217a8622576f8ec07d0b62027/AlgebraicGroups/Algebra/SpecialLinearCoordinateRing.lean#L195-L198) — `formal-frontier-0922`

Snippet: `samples/formal-frontier/formal-frontier-0922.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Ideal.Quotient.liftₐ_comp
- **file**: Mathlib/RingTheory/Ideal/Quotient/Operations.lean
- **derivation**: Ideal.Quotient.liftₐ_comp _ _ _
- **proof_uses_it**: True
- **explanation**: `coordinateRingToPolynomialQuotient` is defined as `Ideal.Quotient.liftₐ (determinantOneIdeal K n) (localizationToPolynomialQuotient K n) _`. `quotient K n` is defined as `Ideal.Quotient.mkₐ K (determinantOneIdeal K n)`. Mathlib's `Ideal.Quotient.liftₐ_comp` says `(liftₐ I f hI).comp (mkₐ R₁ I) = f`. Taking `I = determinantOneIdeal K n` and `f = localizationToPolynomialQuotient K n` gives the theorem after unfolding the two definitions. The library's proof is exactly `Ideal.Quotient.liftₐ_comp _ _ _`.

### [`Steinberg.lift_unique`](https://github.com/FormalFrontier/general-linear-groups/blob/ff8095ef752bcc8bacb5b7b18255fc88470e5e97/GeneralLinearGroups/Steinberg.lean#L154-L161) — `formal-frontier-0924`

Snippet: `samples/formal-frontier/formal-frontier-0924.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: PresentedGroup.toGroup.unique
- **file**: Mathlib/GroupTheory/PresentedGroup.lean
- **derivation**: exact MonoidHom.ext fun _ => PresentedGroup.toGroup.unique _ φ (fun x => hφ x.1 x.2)
- **explanation**: Steinberg.lift is defined as PresentedGroup.toGroup with f := fun gen => f gen.1 gen.2, and generator p a is PresentedGroup.of (p, a). Mathlib's PresentedGroup.toGroup.unique says that any hom g with g (of x) = f x for all x agrees with toGroup h pointwise. Applying it to the specific generating set (Root ι × R), plus MonoidHom.ext and unfolding generator and lift, gives lift_unique. The current proof instead uses the library's own hom_ext, which wraps PresentedGroup.ext, and lift_generator.

### [`LinearMap.postcomp_injective`](https://github.com/FormalFrontier/projective-modules/blob/630c227210958554603cb3f949c6522133d38af3/ProjectiveModules/Module/HomExact.lean#L48-L51) — `formal-frontier-0963`

Snippet: `samples/formal-frontier/formal-frontier-0963.lean`

- **verdict**: `special_case`
- **mathlib_declaration**: Function.Injective.injective_linearMapComp_left
- **file**: Mathlib/Algebra/Module/LinearMap/Defs.lean
- **derivation**: hi.injective_linearMapComp_left
- **proof_uses_it**: True
- **explanation**: Mathlib's `Function.Injective.injective_linearMapComp_left` says that if `f` is injective then `fun g => f.comp g` is injective. The library's `postcomp i` is an additive homomorphism whose underlying function is `fun g => i.comp g`, so the theorem is Mathlib's lemma after unfolding `postcomp`. The library's proof is already exactly `hi.injective_linearMapComp_left`. I did not find a Mathlib lemma stated directly for the library's `postcomp`. The only `postcomp` definitions I saw in Mathlib are for other structures, such as continuous linear maps and category theory.
