# Findings

### concept-reinvention: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L83-L86)

Declaration: `DFinsupp.singleton`

`singleton` is the pointwise postcomposition of `f` with `Finset.singleton`. It rebuilds the support data by hand (`support'.map ...`). That is exactly what `DFinsupp.mapRange` already does for any family of maps `β₁ i → β₂ i` that preserve zero. Here the zero-preservation is `{0} = 0` in `Finset`, which holds under the `Pointwise` scope the file opens.

Proposed change:

Define `singleton f := DFinsupp.mapRange (fun i (a : α i) => ({a} : Finset (α i))) (fun i => singleton_zero) f`, or `Finset.singleton_zero` if that is the actual name. Then derive `mem_singleton_apply_iff` from `mapRange_apply`, which is `rfl`. The manual support proof goes away. You could also drop the bespoke definition. It is only used by the one lemma that follows it, which is unused elsewhere in Mathlib.

Benefit: This removes a hand-written `support'` proof and ties `singleton` to the standard API (`mapRange_apply`, `mapRange` lemmas). A reader no longer has to re-verify the support argument.

Source evidence:

- `DFinsupp.mapRange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Defs.lean`: def mapRange (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (x : Π₀ i, β₁ i) : Π₀ i, β₂ i :=
- `Finset.singleton_one (additive: singleton_zero)` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean`: theorem singleton_one : ({1} : Finset α) = 1 :=

### concept-reinvention: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L98-L110)

Declaration: `DFinsupp.rangeIcc`

`rangeIcc f g` is the pointwise binary combination `i ↦ Icc (f i) (g i)` of two `DFinsupp`s. `DFinsupp.zipWith` already provides this, including the support proof (`xs + ys` with the `bind`/`map` structure). The file re-proves that construction by hand with `Multiset.notMem_mono` and `le_add_left/right`. The only side condition is `Icc 0 0 = 0`, i.e. `Icc_self 0` and the pointwise `{0} = 0` for `Finset`. The file's own proof already ends with `Icc_self _`.

Proposed change:

Define `rangeIcc f g := DFinsupp.zipWith (fun i (a b : α i) => Icc a b) (fun i => by simpa using Icc_self (0 : α i)) f g` (or a proof using `Icc_self` and `Finset.singleton_zero`). `rangeIcc_apply` stays `rfl` via `zipWith_apply`. The explicit multiset support proof can then be deleted.

Benefit: This is about 10 fewer lines of low-level `Multiset` reasoning. It reuses the standard `zipWith` construction and API. The `rangeIcc` definition now reads like its `Finsupp` counterpart, which is also a pointwise `Icc`.

Source evidence:

- `DFinsupp.zipWith` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Defs.lean`: def zipWith (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i) :
- `DFinsupp.zipWith_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Defs.lean`: mapRange f hf g i = f i (g i)
- `DFinsupp.zipWith_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Defs.lean`: zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=

### concept-reinvention: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L44-L46)

Declaration: `Finset.indicator'`

The file defines its own indicator vector of a finset. Mathlib already has the indicator-function concept as `Set.indicator`. The same function is `Set.indicator (S : Set U) (1 : U → ℝ)`, with `Set.indicator_apply` plus `Finset.mem_coe` giving the same `if i ∈ S then 1 else 0` unfolding. Mathlib also has Finset-indexed indicator lemmas, such as `Finset.indicator_biUnion_apply`, which are stated for `Set.indicator`. The custom def is injected into the global `Finset` namespace. It needs its own `@[simp]` apply lemma and its own injectivity proof (`indicator'_injective`). It is used only in this file.

Proposed change:

Drop `Finset.indicator'`. Use `Set.indicator (↑S : Set U) (1 : U → ℝ)`, or a local `abbrev`/notation if brevity is wanted. Replace `indicator'_injective` with a proof from `Set.indicator` lemmas, e.g. `Set.indicator_one_inj` if present, otherwise a short ext argument. Replace the `@[simp] indicator'_apply` lemma with `Set.indicator_apply`. Since `Finset.indicator'` occurs nowhere else in the repo, no other file needs to change.

Benefit: The file reuses Mathlib's simp set and indicator API instead of maintaining a parallel def, apply lemma and injectivity lemma. It also stops adding a non-Mathlib name to the `Finset` namespace. Readers recognise the concept immediately.

Source evidence:

- `Set.mulIndicator (additive: Set.indicator)` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Notation/Indicator.lean`: noncomputable def mulIndicator (s : Set α) (f : α → M) (x : α) : M :=

### concept-reinvention: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L53-L55)

Declaration: `clm_decompose / clm_indicator'_eq_additiveFunction (basis vectors written as Function.update 0 i 1)`

The file repeatedly writes the standard basis vector as `Function.update (0 : U → ℝ) i 1`. Mathlib has the concept `Pi.single i 1`, defined as `Function.update 0 i 1` via the additive version of `Pi.mulSingle`. Mathlib also has `Pi.basisFun`. The decomposition of a linear functional on `U → ℝ` over basis vectors is already `LinearMap.pi_apply_eq_sum_univ`. `clm_decompose` re-proves it by hand for a continuous linear map. The statement uses a bare `update` expression, so Mathlib's `Pi.single` lemmas (`Pi.single_apply`, `Finset.sum_pi_single`, and so on) do not fire. The proof also needs the manual `ext j; simp [Function.update, ...]` steps.

Proposed change:

Write basis vectors as `Pi.single i (1 : ℝ)` in `clm_decompose`, `clm_indicator'_eq_additiveFunction` and the defining `a i := -(Λ (Function.update 0 i 1))`. Derive `clm_decompose` from `LinearMap.pi_apply_eq_sum_univ` applied to `(Λ : (U → ℝ) →ₗ[ℝ] ℝ)`, after rewriting `fun j => if i = j then 1 else 0` to `Pi.single i 1`. Alternatively delete the lemma if it is unused. In this file `clm_decompose` is stated but not referenced in the later proofs I read.

Benefit: This removes a hand-rolled version of an existing Mathlib concept and a duplicate lemma. The standard simp lemmas for `Pi.single` then apply, and the manual `ext`/`simp [Function.update]` proofs get shorter.

Source evidence:

- `Pi.mulSingle (additive: Pi.single)` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Notation/Pi/Basic.lean`: def mulSingle (i : ι) (x : M i) : ∀ j, M j := Function.update 1 i x
- `LinearMap.pi_apply_eq_sum_univ` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/LinearAlgebra/Pi.lean`: theorem pi_apply_eq_sum_univ [Fintype ι] (f : (ι → R) →ₗ[R] M₂) (x : ι → R) :
    f x = ∑ i, x i • f fun j => if i = j then 1 else 0

### concept-reinvention: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L32-L36)

Declaration: `CKN.Leray.l2Vec3Equiv`

This is exactly Mathlib's `EuclideanSpace.equiv (Fin 3) ℝ`. `L2Vec3` is `PiLp 2 (fun _ : Fin 3 => ℝ)`, which is `EuclideanSpace ℝ (Fin 3)`. `EuclideanSpace` is an abbrev, and `EuclideanSpace.equiv` is an abbrev for `PiLp.continuousLinearEquiv 2 𝕜 _`. The file's definition is therefore the same term with the arguments filled in, and it is a duplicate concept. The repo also defines a second `CKN.l2Vec3Equiv` with the same body in `JSpaceFourierPotentialBase.lean`, so it has now been written twice.

Proposed change:

Delete the local `def`. Use `EuclideanSpace.equiv (Fin 3) ℝ` directly. If a short name is wanted, make it an `abbrev` or notation for that, and keep one copy (also replacing the duplicate in `JSpaceFourierPotentialBase.lean`). The `l2Vec3Equiv` call sites in this file should continue to typecheck, because the two terms are defeq.

Benefit: There is no private parallel definition to keep in sync. Readers see at once that this is the standard coordinate equivalence on Euclidean space. The two copies of `l2Vec3Equiv` in the repo are merged, and Mathlib's existing lemmas about `EuclideanSpace.equiv` become directly usable.

Source evidence:

- `EuclideanSpace.equiv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: abbrev EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜 :=
  PiLp.continuousLinearEquiv 2 𝕜 _
- `CKN.l2Vec3Equiv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/JSpaceFourierPotentialBase.lean`: def l2Vec3Equiv : L2Vec3 ≃L[ℝ] Vec3 :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)

### concept-reinvention: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L42-L49)

Declaration: `CKN.Leray.l2BasisVec (with private l2BasisVec_norm and inner_l2BasisVec)`

`l2BasisVec i` is `toLp 2 (Pi.single i 1)` on `PiLp 2 (fun _ => ℝ)`. `CKN.basisVec i` unfolds to `Pi.single i 1`. This is Mathlib's `EuclideanSpace.single i 1`, which is an abbrev for `PiLp.single 2 i 1 := toLp p (Pi.single i a)`. It is also the standard orthonormal basis `EuclideanSpace.basisFun (Fin 3) ℝ i`. Mathlib already has `PiLp.norm_single`, `EuclideanSpace.single_apply`, `EuclideanSpace.inner_single_right` and `EuclideanSpace.basisFun_apply`. The file re-proves the norm fact in `l2BasisVec_norm` and the inner-product fact in `inner_l2BasisVec` by unfolding `simp`. The repo also has a second copy under the name `l2BasisVec3` in `JSpaceFourierPotentialBase.lean`.

Proposed change:

Remove `l2BasisVec`. Use `EuclideanSpace.single i (1 : ℝ)` (or `EuclideanSpace.basisFun (Fin 3) ℝ i`) in `gradientOfCovectorLinear` and throughout. Replace `l2BasisVec_norm` by `PiLp.norm_single` followed by `norm_one`. Replace `inner_l2BasisVec` by `EuclideanSpace.inner_single_right` (it gives `1 * conj (ξ i)`, which simplifies with `simp`). Merge with `l2BasisVec3` in the other file.

Benefit: This removes a locally defined basis vector, which in turn removes a norm lemma and an inner-product lemma that Mathlib already supplies. It also gives the definition the standard name that readers and automation recognise, and avoids duplicates inside the repo.

Source evidence:

- `EuclideanSpace.single` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: abbrev EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι := PiLp.single 2 i a
- `PiLp.single` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Normed/Lp/PiLp.lean`: def single (i : ι) (a : β i) : PiLp p β := toLp p (Pi.single i a)
- `PiLp.norm_single` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Normed/Lp/PiLp.lean`: lemma norm_single (i : ι) (b : β i) : ‖single p i b‖ = ‖b‖
- `CKN.l2BasisVec3` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/JSpaceFourierPotentialBase.lean`: WithLp.toLp 2 (Pi.single i (1 : ℝ))

### statement-generality: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L186-L197)

Declaration: `DFinsupp.card_Iic / DFinsupp.card_Iio (section IsBotZeroClass)`

`card_Iic` and `card_Iio` assume `AddCommMonoid (α i)`, but no addition is used. `IsBotZeroClass` only needs `[LE α] [Zero α]`, and the lemmas only need `Icc`, `bot = 0` and `Iic_eq_Icc`. The `AddCommMonoid` binder is there only because the `OrderBot (Π₀ i, α i)` and `IsBotZeroClass (Π₀ i, α i)` instances in `DFinsupp/Order.lean` are stated under a blanket `[∀ i, AddCommMonoid (α i)]`. That `variable` line is shared with the `CanonicallyOrderedAdd` lemmas further down the section. It makes these two lemmas needlessly specialised: they are unavailable for types that have a `Zero`, a partial order and a bottom `0` but no addition.

Proposed change:

In `DFinsupp/Order.lean`, state the two instances (`OrderBot` and `IsBotZeroClass` on `Π₀ i, α i`) under `[∀ i, Zero (α i)] [∀ i, LE (α i)]`, or `[∀ i, PartialOrder (α i)]`. The existing proofs `bot_le := by simp [le_def]` and `isBot_zero := isBot_bot` do not use addition. Then change line 189 of the target to `variable [∀ i, Zero (α i)] [∀ i, PartialOrder (α i)] [∀ i, IsBotZeroClass (α i)]`. The statements and proofs of `card_Iic` and `card_Iio` stay as they are. The `Finsupp` counterpart of these lemmas has the same over-strong binder and could be changed in the same way.

Benefit: The cardinality formulas apply to any family with `Zero`, a partial order and a bottom `0`, without inventing an additive structure. The hypotheses then match the actual mathematical content, and the lemma signature says that only `0 = ⊥` is relevant.

Source evidence:

- `IsBotZeroClass` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Algebra/Order/IsBotOne.lean`: class IsBotZeroClass (α : Type*) [LE α] [Zero α] : Prop where
- `OrderBot (Π₀ i, α i) instance` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Order.lean`: variable (α) [∀ i, AddCommMonoid (α i)] [∀ i, PartialOrder (α i)]
- `OrderBot (Π₀ i, α i) instance` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Order.lean`: bot_le := by simp [le_def]

### statement-generality: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L292)

Declaration: `Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow / Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow`

The same statement is proved twice, once for functions on ℝ at `atTop` and once for functions on ℕ at `atTop` composed with the cast. The proofs are line-for-line the same, except for a `Nat.one_le_cast` step. The statement only uses that the argument of `^` is a real function tending to `atTop`, so both lemmas specialise one more general result. Users who need other domains, such as `⌊t⌋₊` or `2 ^ n`, must compose with `comp_tendsto` and re-derive the bounds. `SumCoeff.lean` already does this with `hO.comp_tendsto tendsto_nat_floor_atTop`.

Proposed change:

State one lemma over an arbitrary filter and a real-valued function tending to `atTop`:
`theorem IsBigO.mul_rpow_of_tendsto_atTop {α : Type*} {l : Filter α} {u : α → ℝ} (hu : Tendsto u l atTop) {f g : α → E} (hf : f =O[l] fun x ↦ u x ^ a) (hg : g =O[l] fun x ↦ u x ^ b) (h : a + b ≤ c) : (f * g) =O[l] fun x ↦ u x ^ c`.
The proof is the existing one. Start with `refine (hf.mul hg).trans (Eventually.isBigO ?_)`. Then use `filter_upwards [hu.eventually_ge_atTop 1] with t ht`. Rewrite with `Real.rpow_add (zero_lt_one.trans_le ht)` and `Real.norm_of_nonneg`. Finish with `Real.rpow_le_rpow_of_exponent_le ht h`. This needs no case analysis. Keep the two current lemmas as one-line corollaries, using `tendsto_id` and `tendsto_natCast_atTop_atTop` for `u`. Unlike the current copies, these corollaries would not repeat the proof.

Benefit: This removes the duplicated proof and covers other index types and filters, such as sequences `n ↦ u n` or `t ↦ ⌊t⌋₊`, without reproving the bound. It also makes explicit that only `u → ∞` is used, so users no longer need `comp_tendsto` first. The mathematical content is unchanged and the degenerate cases (a, b, c of any sign) are handled by the same `1 ≤ u x` argument.

Source evidence:

- `IsBigO.mul_atTop_rpow_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: filter_upwards [eventually_ge_atTop 1] with t ht
- `lemma₁` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/NumberTheory/LSeries/SumCoeff.lean`: exact (hO.comp_tendsto tendsto_nat_floor_atTop).trans <|
- `IsBigO.comp_tendsto` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/Asymptotics/Basic.lean`: theorem IsBigO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l)

### statement-generality: [TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L116-L127)

Declaration: `Matrix.SpecialOrthogonalGroup.eq_one_of_mem_center_of_odd`

The hypothesis `3 ≤ Fintype.card n` is only a side condition for `mem_center_iff`. Odd dimension already gives `1 ≤ Fintype.card n`. The only case the bound excludes is dimension 1, where `specialOrthogonalGroup n R` is trivial because `det g = g default default = 1`. So the odd-dimension triviality is true without `hn`, but the statement is restricted to n ≥ 3 and the docstring repeats the restriction. The intended mathematics is not changed; the statement is just narrower than the truth.

Proposed change:

State the lemma as `theorem eq_one_of_mem_center_of_odd (h2 : IsRegular (2 : R)) (g : specialOrthogonalGroup n R) (hodd : Odd (Fintype.card n)) (hg : g ∈ Subgroup.center (specialOrthogonalGroup n R)) : g = 1`. For the proof, do `by_cases hn : 3 ≤ Fintype.card n`. If it holds, run the current argument unchanged. Otherwise `Odd (card n)` forces `Fintype.card n = 1`, since card 0 is even and card 2 is even. Then `Fintype.card_eq_one_iff` gives a `Unique n`. `Matrix.det_unique` together with `(mem_specialOrthogonalGroup_iff.mp g.2).2` shows the single entry is 1, and `Subtype.ext` plus `ext i j` (with i = j = default) closes the goal. Equivalently, the 1×1 case could be a separate lemma.

Benefit: Callers no longer have to prove an artificial `3 ≤ n` for odd n. The downstream `eq_one_of_isCentralPoint_of_odd` needs `hn` only for `isCentralPoint_iff_mem_center_pointsMulEquiv`, so it also becomes easier to generalise. The result becomes the clean statement that every odd-dimensional special orthogonal group has trivial center, with n = 1 covered.

Source evidence:

- `TauCeti.SpecialOrthogonal.eq_one_of_isCentralPoint_of_odd` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/AlgebraicGroup/SpecialOrthogonal/Center.lean`: (pointsMulEquiv R n (A := A) g) (by simpa using hn) (by simpa using hodd)
- `Matrix.SpecialOrthogonalGroup.mem_center_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean`: have hdet := (mem_specialOrthogonalGroup_iff.mp g.2).2

### statement-generality: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L497-L507)

Declaration: `KaltonRoberts.dual_certificate_exists_proof (with dual_cert_zero_case, dual_cert_pos_case, distToAdditive_nonneg)`

The theorem and its case wrappers are stated only for the specific value `distToAdditive f`. The proof never uses any property of that value. The hypotheses `hM` and `hbest` are phrased purely in terms of the number `M`. The core lemmas `zero_mem_convexHull_of_best_approx` and `dual_cert_from_convexHull` already take an arbitrary `M`. The wrappers `dual_cert_zero_case` (line 82) and `dual_cert_pos_case` (line 478) re-specialise to `distToAdditive f`. This hides a general fact: whenever `M` bounds `|f|` and no additive function approximates `f` uniformly within `M`, a dual certificate for `M` exists. The `hf : IsApproxAdditive f 1` hypothesis is also only used for `f ∅ = 0`. That is not needed for `0 ≤ M`, because `hM ∅` already gives `0 ≤ |f ∅| ≤ M`.

Proposed change:

State the theorem for an arbitrary real `M`:

theorem dual_certificate_exists_of_bound (f : Finset U → ℝ) (M : ℝ)
    (hM : ∀ S : Finset U, |f S| ≤ M)
    (hbest : ∀ a : U → ℝ, ∃ S : Finset U, |f S - additiveFunction a S| ≥ M) :
    Nonempty (DualCertificate f M)

Proof sketch: `0 ≤ M` follows from `(abs_nonneg _).trans (hM ∅)`. If `M = 0`, run the existing zero-case argument with `hM` giving `f S = 0` for all `S`. Otherwise `0 < M`, and `dual_cert_from_convexHull f M` combined with `zero_mem_convexHull_of_best_approx f M` applies directly. Restate `dual_cert_zero_case` with `(M) (hM0 : M = 0)`. Then `dual_certificate_exists_proof` becomes the instance `M := distToAdditive f`, and `hf` is no longer needed in the proof chain.

Benefit: Users get the Hahn–Banach duality statement for any `M`, for example a candidate bound they have computed, without first identifying it with the infimum `distToAdditive f`. The `IsApproxAdditive` hypothesis and the dependence on `iInf`/`iSup` no longer appear in the proof chain. The statement also shows exactly which properties are used. The existing theorem in Lemmas.lean (line 316) follows by a one-line specialisation.

Source evidence:

- `dual_cert_from_convexHull` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: lemma dual_cert_from_convexHull
    (f : Finset U → ℝ) (M : ℝ) (hM_pos : 0 < M)
- `dual_certificate_exists` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Lemmas.lean`:     Nonempty (DualCertificate f (distToAdditive f)) :=
  dual_certificate_exists_proof f _hf _hM _hbest
- `DualCertificate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: structure DualCertificate {U : Type*} [DecidableEq U] [Fintype U]
    (f : Finset U → ℝ) (M : ℝ) where

### statement-generality: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L65-L71)

Declaration: `KaltonRoberts.clm_indicator'_eq_additiveFunction (and clm_decompose)`

The statement quantifies over continuous linear maps `(U → ℝ) →L[ℝ] ℝ`, but the proof only uses `map_sum`, that is additivity. Continuity plays no role. `clm_decompose` (line 53) likewise only uses `map_smul` and `map_sum`. The restriction to continuity is unnecessary. It forces a caller holding an additive or linear map to build a CLM first.

Proposed change:

Generalise to any additive-map class, for example `{F : Type*} [FunLike F (U → ℝ) ℝ] [AddMonoidHomClass F (U → ℝ) ℝ] (Λ : F)`. Alternatively use `(U → ℝ) →ₗ[ℝ] ℝ`. The proof is unchanged: rewrite `S.indicator'` as a sum of `Function.update 0 i 1`, then use `map_sum`. The existing call in `zero_mem_convexHull_of_best_approx` still works, since `(U → ℝ) →L[ℝ] ℝ` has these instances. `clm_decompose` could similarly take `LinearMapClass`.

Benefit: The lemma becomes usable for plain linear or additive functionals, for example on finite-dimensional spaces where continuity is automatic. It states more precisely what the proof relies on, and the name can drop the `clm_` prefix.

Source evidence:

- `clm_indicator'_eq_additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`:   rw [this, map_sum]; rfl

### statement-generality: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L95-L99)

Declaration: `CKN.Leray.fourier_postcompCLM`

The lemma is stated only for Schwartz maps on the specific space `L2Vec3`. The proof uses nothing about that space. It only needs the Fourier integral formula `Real.fourier_eq`, integrability of Schwartz maps, and `ContinuousLinearMap.integral_comp_comm`. Mathlib builds the Schwartz-space Fourier transform on any real inner product space `V` that is finite-dimensional and has `[MeasurableSpace V] [BorelSpace V]`, so the lemma is needlessly specialised. It is also a generic fact about Schwartz maps that Mathlib lacks, and its name suggests a general result.

Proposed change:

Replace `L2Vec3` by a variable `{V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]`. The statement becomes `theorem fourier_postcompCLM {V F G : Type*} ... (L : F →L[ℂ] G) (f : SchwartzMap V F) : 𝓕 (f.postcompCLM L) = (𝓕 f).postcompCLM L`. Keep the proof, replacing `L2Vec3` by `V` in the `change` and `calc` lines. Existing uses at `L2Vec3` unify with the general statement by instance resolution, so no call site changes. This depends on the usual `MeasureSpace V` instance for finite-dimensional inner product spaces, as in the Mathlib Schwartz Fourier section.

Benefit: The lemma becomes reusable for Schwartz maps on any finite-dimensional inner product space. It could be upstreamed next to `SchwartzMap.fourier_fderivCLM_eq`. It also removes a misleading dependence on the `L2Vec3` model, and every existing use keeps working.

Source evidence:

- `SchwartzMap.fourierTransformCLM (section variables)` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`: {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
- `Real.fourier_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Fourier/FourierTransform.lean`: lemma fourier_eq (f : V → E) (w : V) :
    𝓕 f w = ∫ v, 𝐞 (-⟪v, w⟫) • f v := rfl
- `schwartzDivergence Fourier lemma (use of fourier_postcompCLM)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierJApproximationOrthogonality.lean`: have hpost := fourier_postcompCLM divergenceTrace

### statement-generality: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L270-L280)

Declaration: `sectorCurve_norm_on_arc / sectorCurve_norm_seg1 / sectorCurve_norm_seg3'`

Three norm lemmas assume the strict condition `0 < r`. Their proofs only use `le_of_lt hr` to feed `Complex.norm_of_nonneg`, which needs a nonnegativity hypothesis. The same holds for `sectorCurve_norm_on_arc` (lines 154–159) and `sectorCurve_norm_seg3'` (lines 277–280). The statements are true for `0 ≤ r`, including the degenerate curve r = 0, which is constantly 0. The strict hypothesis is stronger than the result needs. It stops these lemmas applying to the degenerate r = 0 sector curve, or to a radius only known to be nonnegative.

Proposed change:

Change the hypothesis in all three lemmas from `(hr : 0 < r)` to `(hr : 0 ≤ r)`, and replace `le_of_lt hr` by `hr` in the proofs. For example: `theorem sectorCurve_norm_seg1 (r : ℝ) (hr : 0 ≤ r) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 0 1) : ‖sectorCurve r α t‖ = t * r`, with proof `rw [sectorCurve_seg1 r α t ht]; exact Complex.norm_of_nonneg (mul_nonneg ht.1 hr)`. The arc lemma becomes `Complex.norm_of_nonneg hr` after the simp, and the segment-3 lemma uses `mul_nonneg (by linarith [ht.2]) hr`. Existing callers pass `hr : 0 < r`. They can pass `hr.le`, or `le_of_lt hr`, at the call sites. The affected call sites in this file are lines 320, 338, 361, 423, 511, 568, 598 and 607. The callers in SectorCurveLemma.lean also need the same edit.

Benefit: The lemmas then state exactly what the proofs use, a nonnegative radius. They also cover the degenerate case r = 0 (where both sides are 0), and they are easier to reuse in settings where only 0 ≤ r is known. Callers lose nothing, since `hr.le` is immediate.

Source evidence:

- `Complex.norm_of_nonneg` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Complex/Norm.lean`: protected theorem norm_of_nonneg {r : ℝ} (h : 0 ≤ r) : ‖(r : ℂ)‖ = r :=
- `sectorCurve_norm_on_arc` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: exact Complex.norm_of_nonneg (le_of_lt hr)
- `sectorCurve_norm_seg3'` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: Complex.norm_of_nonneg (mul_nonneg (by linarith [ht.2]) (le_of_lt hr))]

### vacuity-and-misstatement: [Mathlib/Data/Finsupp/PWO.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Finsupp/PWO.lean#L20-L21)

Declaration: `module docstring (Main statements) vs Finsupp.wellQuasiOrderedLE`

The module docstring names a main statement `Finsupp.isPWO`. It describes it as holding for a fintype index and a codomain that is a well-ordered linear order. No such declaration exists in the file. A grep of the Mathlib tree finds `Finsupp.isPWO` only in this docstring. The only result in the file is the instance `Finsupp.wellQuasiOrderedLE`. That instance has different hypotheses: `Finite σ` instead of `Fintype σ`, and a `Preorder` with `WellQuasiOrderedLE` instead of a well-ordered linear order. Its conclusion is `WellQuasiOrderedLE (σ →₀ α)` rather than an `IsPWO` statement about a set. A reader following the documentation would look for a nonexistent theorem. They would also believe the result needs a linear order, which is a stricter condition than the file proves.

Proposed change:

Rewrite the 'Main statements' entry to describe the actual result. For example: `* Finsupp.wellQuasiOrderedLE` - Dickson's lemma: `σ →₀ α` is well-quasi-ordered when `σ` is finite and `α` is a well-quasi-ordered preorder with `Zero`. Update the introductory paragraph to say 'finite type' and 'well-quasi-ordered preorder' instead of 'fintype' and 'linear order that is well ordered'. If the `Set.IsPWO` formulation is still wanted, state it explicitly. It can be obtained from the instance via `WellQuasiOrderedLE`/`IsPWO` lemmas, but I have not checked which lemma names apply.

Benefit: The documentation would match the declared result and its true generality. Readers and search tools would no longer look for a missing `Finsupp.isPWO`. They would also see that the result needs only a preorder and a finite index type.

Source evidence:

- `Finsupp.wellQuasiOrderedLE` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/Finsupp/PWO.lean`: instance Finsupp.wellQuasiOrderedLE {α σ : Type*} [Zero α] [Preorder α] [WellQuasiOrderedLE α]
    [Finite σ] : WellQuasiOrderedLE (σ →₀ α) :=

### vacuity-and-misstatement: [Mathlib/Topology/Category/Profinite/EffectiveEpi.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L55-L63)

Declaration: `Profinite.profiniteToCompHausEffectivePresentation`

The docstring does not match the declaration. It says the presentation is of `X : Profinite` with respect to the inclusion functor from `Stonean`. The declaration takes `X : CompHaus` and gives an `EffectivePresentation` for the functor `profiniteToCompHaus`, which is the inclusion of `Profinite` into `CompHaus`. The presenting object `p` is `Stonean.toProfinite.obj X.presentation`, which is a Profinite object. So the docstring names the wrong object type and the wrong functor. A reader would take this as a statement about presenting Profinite spaces by Stonean ones. The def actually shows that `profiniteToCompHaus` is effectively enough, by presenting a CompHaus space with a Profinite space.

Proposed change:

Reword the docstring, for example: "An effective presentation of `X : CompHaus` with respect to the inclusion functor `profiniteToCompHaus`. The presenting profinite set is the underlying profinite set of the extremally disconnected presentation of `X`."

Benefit: The documentation then states what the def proves. It no longer suggests a Profinite-by-Stonean presentation that is not what is formalised.

Source evidence:

- `Profinite.profiniteToCompHausEffectivePresentation` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean`: noncomputable def profiniteToCompHausEffectivePresentation (X : CompHaus) :
    profiniteToCompHaus.EffectivePresentation X where

### vacuity-and-misstatement: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L497-L505)

Declaration: `KaltonRoberts.dual_certificate_exists_proof`

The headline Lemma 2.1 theorem assumes `hbest`, which the `Fintype U` instance already makes true for every `f`. `distToAdditive f` is the infimum over `a` of the supremum over the finite family of `S`. So for each `a` the supremum is at least the infimum, and by finiteness it is attained at some `S`. The sibling lemma `best_approx_property` in Pipeline.lean proves exactly this from `distToAdditive g = M`, which is `rfl` here. The statement therefore looks conditional on a 'best approximation' hypothesis, but that hypothesis adds nothing. The only real content is `hM`, which says `a = 0` attains the distance. The docstring does not say this. The same redundant `hbest` is repeated in `dual_cert_pos_case` and in the wrapper in Lemmas.lean. This does not make the theorem false or vacuous. It makes the hypotheses mislead about what is assumed and what is proved.

Proposed change:

Drop `hbest` from `dual_certificate_exists_proof` and `dual_cert_pos_case`. Inside `dual_cert_pos_case`, derive it for `distToAdditive f` with the argument used in `best_approx_property`, using `ciInf_le`/`csInf_le` plus `exists_eq_ciSup_of_finite` or `Finset.exists_max_image`. The Pipeline.lean lemma could be moved earlier and reused. Keep `hbest` as a hypothesis only on the internal Hahn–Banach lemma `zero_mem_convexHull_of_best_approx`, where `M` is a free parameter. Update the docstring to say that `hM` expresses that `0` is a closest additive approximant.

Benefit: The public statement then lists only the assumptions that carry content (`hf`, `hM`). Callers such as Lemmas.lean no longer need to supply a hypothesis that is automatic, and readers are no longer led to think Lemma 2.1 depends on an extra optimality condition.

Source evidence:

- `best_approx_property` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Pipeline.lean`: lemma best_approx_property [Finite U] (g : Finset U → ℝ) (M : ℝ)
- `distToAdditive` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: ⨅ a : U → ℝ, ⨆ S : Finset U, |f S - additiveFunction a S|
- `exists_eq_ciSup_of_finite` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Order/ConditionallyCompleteLattice/Finset.lean`: theorem exists_eq_ciSup_of_finite [Nonempty ι] [Finite ι] {f : ι → α} : ∃ i, f i = ⨆ i, f i

### missing-structure: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L83-L86)

Declaration: `DFinsupp.singleton`

`DFinsupp.singleton` is the pointwise image of `f` under `Finset.singleton`, which sends `0` to `0 = {0}` in the pointwise `Finset` zero. That is exactly what `DFinsupp.mapRange` provides. Instead the file proves the support-witness field by hand and only gets the apply lemma by `rfl`. The result does not reuse the `mapRange` API (`mapRange_apply`, `mapRange_zero`, `mapRange_def`, `support_mapRange`). Mathlib already supplies the zero-preservation fact as `Finset.singleton_zero` and the bundled `Finset.singletonZeroHom`.

Proposed change:

Define `def singleton (f : Π₀ i, α i) : Π₀ i, Finset (α i) := f.mapRange (fun _ => Finset.singleton) (fun _ => Finset.singleton_zero)`, using the existing `Finset.singleton_zero`. Here `Finset.singleton` is the function `a ↦ {a}`. Then `mem_singleton_apply_iff` can be proved via `mapRange_apply`/`mem_singleton`. A `support_singleton_subset` lemma would follow from `support_mapRange`.

Benefit: This removes a manual `Multiset`-level support proof. It shows that `singleton` is a `mapRange`, and it gives `mapRange_zero`, `support_mapRange` and the other `mapRange` lemmas for free. It also makes `singleton` agree with the `Finset.singletonZeroHom` structure instead of re-deriving the same zero-preservation.

Source evidence:

- `DFinsupp.mapRange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Defs.lean`: def mapRange (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (x : Π₀ i, β₁ i) : Π₀ i, β₂ i :=
- `Finset.singleton_one (additive: singleton_zero)` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean`: theorem singleton_one : ({1} : Finset α) = 1 :=
- `Finset.singletonOneHom (additive: singletonZeroHom)` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Algebra/Group/Pointwise/Finset/Basic.lean`: def singletonOneHom : OneHom α (Finset α) where

### missing-structure: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L98-L109)

Declaration: `DFinsupp.rangeIcc`

`rangeIcc f g` is a pointwise binary operation on two `DFinsupp`s with `Icc 0 0 = 0 = {0}`. That is exactly the situation `DFinsupp.zipWith` handles. The file re-proves the support-witness construction by hand (sum of the two multisets, two `Multiset.notMem_mono` arguments, then `Icc_self`). This is the same construction as `zipWith`. As a result, it does not reuse the `zipWith` API (`zipWith_apply`, `zipWith_def`).

Proposed change:

Define `def rangeIcc (f g : Π₀ i, α i) : Π₀ i, Finset (α i) := DFinsupp.zipWith (fun _ => Icc) (fun _ => Icc_self 0) f g`, using `Icc_self : Icc a a = {a}` (the existing `Icc_self` lemma) and `{0} = 0` by `rfl`. Then `rangeIcc_apply` stays `rfl` (or `zipWith_apply`). `support_rangeIcc_subset` can be derived from `zipWith_def` as `mk_support_subset`, or kept as is.

Benefit: This removes about ten lines of low-level `Multiset` support reasoning. It makes explicit that `rangeIcc` is the `zipWith` of `Icc`, and the existing `zipWith` lemmas apply to it. It also parallels the neighbouring `singleton` definition, which would be a `mapRange`.

Source evidence:

- `DFinsupp.zipWith` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Defs.lean`: def zipWith (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i) :
- `DFinsupp.zipWith_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Defs.lean`: (g₂ : Π₀ i, β₂ i) (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
- `DFinsupp.rangeIcc` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: toFun i := Icc (f i) (g i)

### missing-structure: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L513-L556)

Declaration: `LinearMap.taylorComponent (with taylorComponent_zero / taylorComponent_add / taylorComponent_smul)`

taylorComponent b n is b ↦ (letter ∘ₗ b) ∘ₗ of n, which is linear in b. The file states this as three separate preservation lemmas (zero, add, smul) about an unbundled function. It therefore gets none of the LinearMap API, such as map_sum, map_neg, map_sub, or composition with the coderivEquivTaylor map. taylorComponent_add and taylorComponent_smul are not used anywhere in the repo. taylorComponent_zero is used in only two places.

Proposed change:

Bundle the map: define the linear map (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) →ₗ[R] ((n : {n : ℕ // 0 < n}) → TensorPower R n.1 M →ₗ[R] M) as Pi.lift/LinearMap.pi of (LinearMap.lcomp-style) postcomposition with letter via LinearMap.compRight (letter R M) and precomposition with `of R M n`. Keep the pointwise `taylorComponent_apply` as a simp lemma. Then drop the zero/add/smul lemmas and use map_zero, map_add, map_smul and map_sum. Alternatively, keep the arity-wise function but define it from `LinearMap.compRight`/`LinearMap.lcomp` so linearity is inherited.

Benefit: Linearity becomes a single structured fact, and generic lemmas apply directly. Statements such as eq_zero_iff_taylorComponent_eq_zero become injectivity/kernel statements about a bundled linear map. This also matches the already bundled coderivEquivTaylor.

Source evidence:

- `LinearMap.compRight` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Algebra/Module/LinearMap/End.lean`: def compRight (f : M₁ →ₗ[R] M₂) : (M →ₗ[R] M₁) →ₗ[S] M →ₗ[R] M₂ where
- `LinearMap.taylorComponent` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean`: (letter R M ∘ₗ b) ∘ₗ of R M n

### missing-structure: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L153-L178)

Declaration: `zero_mem_convexHull_of_best_approx (use of additiveFunction with scaled/negated weights)`

The passage from a weight function to its additive set function, a ↦ (S ↦ ∑ i ∈ S, a i), is linear in `a`. It is only a bare `def`, so the file keeps unfolding it and redoing sum algebra by hand. Examples: `ring_nf!; unfold additiveFunction; simp [Finset.sum_neg_distrib]` for negation, and `simp only [additiveFunction]` plus `Continuous ... by continuity` for the ε-scaling. The same unfolding appears in Pipeline.lean (`Finset.sum_sub_distrib`, `Finset.sum_add_distrib`, `Finset.sum_neg_distrib`). Facts like `additiveFunction (fun i => ε * a i) S = ε * additiveFunction a S` are re-derived inline each time.

Proposed change:

In Defs.lean, add a bundled map such as `additiveMap : (U → ℝ) →ₗ[ℝ] (Finset U → ℝ)` with `additiveMap a = additiveFunction a`. Alternatively, prove `additiveFunction (c • a) S = c * additiveFunction a S`, `additiveFunction (-a) S = -additiveFunction a S` and the add/sub versions once. The ε-scaling steps could then use `map_smul`/`map_neg`, or `ε * additiveFunction a S` directly, so the continuity argument is a simple `Continuous` statement in ε. The negation step at line 162 would no longer need `unfold`.

Benefit: The sum algebra is done once instead of in every proof. The ε-perturbation argument reads as `|f S - ε * additiveFunction a S|`, as the docstring describes it. It also reduces the repeated unfolding in Pipeline.lean.

Source evidence:

- `additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: fun A => ∑ i ∈ A, a i
- `distToAdditive_sub_additive` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Pipeline.lean`: simp +decide [ additiveFunction, Finset.sum_sub_distrib ]

### missing-structure: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L52-L75)

Declaration: `clm_decompose / clm_indicator'_eq_additiveFunction`

`clm_decompose` hand-proves the coordinate expansion of a linear functional on `U → ℝ`. Mathlib already has this for any `R`-linear map out of `ι → R`, as `LinearMap.pi_apply_eq_sum_univ`. A continuous linear map coerces to a `LinearMap`, so it applies. `clm_decompose` is also unused anywhere in the repository. The correspondence between functionals and their coordinate weights, `Λ ↦ fun i => Λ (Function.update 0 i 1)`, is spelled out with raw `Function.update` in lemmas, rather than through the standard basis vectors `Pi.single i 1` or `Pi.basisFun`.

Proposed change:

Delete `clm_decompose`. If a coordinate formula is needed, derive it from `LinearMap.pi_apply_eq_sum_univ` applied to `(Λ : (U → ℝ) →ₗ[ℝ] ℝ)`. Express the weights as `Λ (Pi.single i 1)` and prove `clm_indicator'_eq_additiveFunction` using `S.indicator' = ∑ i ∈ S, Pi.single i 1` with `map_sum`.

Benefit: This removes an unused 15-line duplicate of Mathlib and links the weight vector `a i = -Λ (single i 1)` to the standard basis API. The repeated `Function.update (0 : U → ℝ) i 1` also becomes `Pi.single i 1`.

Source evidence:

- `LinearMap.pi_apply_eq_sum_univ` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/LinearAlgebra/Pi.lean`: f x = ∑ i, x i • f fun j => if i = j then 1 else 0

### missing-structure: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L44-L62)

Declaration: `l2BasisVec (with l2BasisVec_norm, inner_l2BasisVec, gradientOfCovectorLinear, gradientOfCovectorLinear_norm_bound)`

The standard basis of the Hilbert coordinate space `L2Vec3 = PiLp 2 (fun _ => ℝ)` is re-introduced as a bare function `l2BasisVec : Fin 3 → L2Vec3`. Its facts are then proved by hand as separate private lemmas: unit norm in `l2BasisVec_norm` and the coordinate formula in `inner_l2BasisVec`. Mathlib already provides this as the bundled `OrthonormalBasis` `EuclideanSpace.basisFun (Fin 3) ℝ`. That bundle supplies `basisFun_apply`, `basisFun_repr`, `inner_basisFun_real` (`inner ℝ x (basisFun ι ℝ i) = x i`), and orthonormality, which gives `‖b i‖ = 1`. The repo defines the same object again as `l2BasisVec3` in JSpaceFourierPotentialBase.lean, with its own `inner_l2BasisVec3`. So there are two parallel copies of this basis and its inner-product lemma.

Proposed change:

Drop `l2BasisVec`, `l2BasisVec_norm` and `inner_l2BasisVec`. Use `b := EuclideanSpace.basisFun (Fin 3) ℝ`, treating `L2Vec3` as `EuclideanSpace ℝ (Fin 3)`, since they are defeq. Use `b i` in `gradientOfCovectorLinear` and in `weakTestGradientSchwartz_apply`. Get the coordinate formula from `EuclideanSpace.inner_basisFun_real` and the unit norm from `b.orthonormal.1 i` (or `OrthonormalBasis.norm_eq_one`). Consider doing the same for `l2BasisVec3` so the repo has one basis. If the `Pi.single`-based definition must stay, state `l2BasisVec i = EuclideanSpace.basisFun _ ℝ i` once and reuse the Mathlib API. `gradientOfCovectorLinear D` is then the coordinate vector `(D (b i))ᵢ`, which could also be expressed through `b.repr`.

Benefit: This removes two hand-written lemmas here and one duplicate definition and lemma elsewhere. Readers see that the basis is the standard orthonormal basis of Euclidean space, and the file gains orthonormal-basis tools such as `b.repr`, `b.sum_repr` and `b.sum_inner_mul_inner`. Those tools can also shorten the 2-bound proof in `gradientOfCovectorLinear_norm_bound`.

Source evidence:

- `EuclideanSpace.basisFun` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: noncomputable def basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι) :=
- `EuclideanSpace.inner_basisFun_real` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: inner ℝ x (basisFun ι ℝ i) = x i
- `l2BasisVec3` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/JSpaceFourierPotentialBase.lean`: def l2BasisVec3 (i : Fin 3) : L2Vec3 :=
  WithLp.toLp 2 (Pi.single i (1 : ℝ))
- `inner_l2BasisVec3` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/JSpaceFourierPotentialBase.lean`: inner ℝ ξ (l2BasisVec3 i) = frequencyL2Coord i ξ

### simp-interface: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L83-L89)

Declaration: `DFinsupp.singleton / DFinsupp.mem_singleton_apply_iff`

The bundled `DFinsupp.singleton` has no `rfl` application lemma, although the sibling `rangeIcc` has the simp lemma `rangeIcc_apply`. Because `singleton` is a plain def, `simp` cannot rewrite `f.singleton i` to `{f i}`. The only available lemma, `mem_singleton_apply_iff`, is not tagged simp. So `a ∈ f.singleton i` does not normalise to `a = f i`. Only that membership form can be rewritten by hand with the lemma, and the apply form `⇑(f.singleton) i` is stuck.

Proposed change:

Add `@[simp] theorem singleton_apply (f : Π₀ i, α i) (i : ι) : f.singleton i = {f i} := rfl`, mirroring `rangeIcc_apply`. With it, `mem_singleton_apply_iff` follows by `simp` through `Finset.mem_singleton`. Alternatively, mark `mem_singleton_apply_iff` as simp. The normal form is `{f i}`, then `a = f i`, and neither rule can loop.

Benefit: Goals that mention `f.singleton i` or `a ∈ f.singleton i` simplify automatically, as they do for `rangeIcc`. This makes the two bundled-finset constructors consistent, and users no longer have to unfold `singleton` by hand.

Source evidence:

- `DFinsupp.rangeIcc_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: theorem rangeIcc_apply (f g : Π₀ i, α i) (i : ι) : f.rangeIcc g i = Icc (f i) (g i) := rfl

### simp-interface: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L153-L165)

Declaration: `zero_mem_convexHull_of_best_approx (uses of additiveFunction in simp calls)`

`additiveFunction` has no simp lemma for applying it to a finset, such as `additiveFunction a S = ∑ i ∈ S, a i`. The file therefore unfolds the definition by hand with `unfold additiveFunction` or `simp ... [additiveFunction]`. This pattern occurs at lines 157, 164, 176, 191 and 223. Every one of these is a `simp_all` over a large context, and several are followed by a long `simp_all +decide only [...]` list that has to move the `-`, `*` and `∑` around (`mul_neg`, `sum_neg_distrib`, `← Finset.mul_sum`). Unfolding the definition by name is brittle: it exposes the raw `fun A => ∑ ...` body, and the simp set must then be tuned by hand each time. It also gives no stable normal form for expressions such as `additiveFunction (fun i => ε * a i) S`.

Proposed change:

Next to the definition (Defs.lean) or in this file, add `@[simp] lemma additiveFunction_apply (a : U → ℝ) (S : Finset U) : additiveFunction a S = ∑ i ∈ S, a i := rfl`. Optionally add scalar lemmas such as `additiveFunction (fun i => c * a i) S = c * additiveFunction a S` and one for negation, oriented so the scalar moves outside. Then replace the `unfold additiveFunction` and `[additiveFunction]` calls with plain `simp`. Check whether the long `only` lemma lists can shrink.

Benefit: The proofs of the sign facts and of the small-ε argument become shorter and less fragile. Downstream files get a canonical normal form for `additiveFunction` instead of each proof re-unfolding the definition.

Source evidence:

- `additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: fun A => ∑ i ∈ A, a i

### simp-interface: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L268-L273)

Declaration: `indicator'_injective and the Finset.indicator' simp interface`

The file declares `@[simp] Finset.indicator'_apply`, but the proofs ignore it and unfold the definition with `simp [Finset.indicator', ...]` (lines 74, 271), `indicator'` in simp lists (lines 355 and 417 area) and `Finset.indicator'` (line 427). This makes the simp lemma largely redundant and means the intended normal form `if i ∈ S then 1 else 0` is reached by unfolding rather than by the lemma. Also, `indicator'_injective` is used repeatedly as `indicator'_injective.eq_iff` inside simp sets (lines 348, 406, 423), because no simp lemma `S.indicator' = T.indicator' ↔ S = T` exists. The negated form `-S.indicator' = -T.indicator'` is handled only by combining `neg_inj` with that lemma.

Proposed change:

Mark the definition irreducible for simp purposes by relying on `indicator'_apply` and drop `Finset.indicator'` from the simp sets. Add `@[simp] lemma indicator'_inj {S T : Finset U} : S.indicator' = T.indicator' ↔ S = T := indicator'_injective.eq_iff` after `indicator'_injective`. Replace the manual `indicator'_injective.eq_iff` entries in the simp lists with it.

Benefit: There is one canonical simp interface for `indicator'`, namely evaluation and equality. The proofs of `dual_cert_from_convexHull` then need shorter simp lists. Unfolding the definition is no longer needed, so changes to its body would not break proofs.

Source evidence:

- `Finset.indicator'_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: S.indicator' i = if i ∈ S then (1 : ℝ) else 0 := rfl
- `dual_cert_from_convexHull` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: simp +contextual [indicator'_injective.eq_iff]

### simp-interface: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L247-L250)

Declaration: `realPartVectorL2Representative`

The sibling definition `realVectorL2Representative` has a public evaluation lemma `realVectorL2Representative_apply`, which other files use to rewrite. `realPartVectorL2Representative` has no such lemma. The proofs of `realPart_isWeakDivFree_of_fourierOrthogonal` and `realPartVectorL2Representative_eq_ae` therefore unfold the definition by name inside simp calls, together with `l2Vec3Equiv`. They also need an explicit `change` on a hypothesis to expose the coordinate form. The simp normal form is not pinned down, and the unfolding can expose the `ofLp`/`toLp` structure of `PiLp`.

Proposed change:

After the definition, add `theorem realPartVectorL2Representative_apply (v : ComplexVectorL2) (x : Vec3) : realPartVectorL2Representative v x = l2Vec3Equiv (realPartValue (v (WithLp.toLp 2 x))) := rfl`, or state the `ofLp` form that `realVectorL2Representative_apply` uses. Mark it `@[simp]` (or `@[simp, nolint simpNF]` if needed), and use it in place of the unfolding at lines 325 and 360. Together with the `l2Vec3Equiv` apply lemma below, this lets `simp` rewrite both representatives to coordinate form without unfolding the definitions.

Benefit: The real-part representative gets the same rewrite interface as the real one. Later proofs rewrite with one named lemma instead of unfolding the definition, and the `change ... at hp` workaround in the divergence-free proof becomes unnecessary.

Source evidence:

- `realVectorL2Representative_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/ForcePressureGradientClosure.lean`: realVectorL2Representative u x = WithLp.ofLp (u (WithLp.toLp 2 x))
- `realPartVectorL2Representative_eq_ae` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: simp [realVectorL2Representative, realPartVectorL2Representative, hx]
- `realPart_isWeakDivFree_of_fourierOrthogonal` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: simpa [F, realPartVectorL2Representative, l2Vec3Equiv] using hp

### simp-interface: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L33-L36)

Declaration: `l2Vec3Equiv`

`l2Vec3Equiv` is a public `@[expose]` definition with no simp lemma for application, for `l2Vec3Equiv x i`, or for its action on `l2BasisVec`. Every proof that needs its value passes the definition name to simp. Examples are `simp [l2BasisVec, l2Vec3Equiv, CKN.basisVec, Pi.single_apply]` and `simpa [F, realPartVectorL2Representative, l2Vec3Equiv] using hp`, and a similar call in `JSpaceFourierPotentialBase`. Unfolding drags in the `PiLp.continuousLinearEquiv` machinery, so each caller rediscovers the same normal form.

Proposed change:

Add `theorem l2Vec3Equiv_apply (x : L2Vec3) : l2Vec3Equiv x = WithLp.ofLp x := rfl` or the `∀ i` coordinate form `l2Vec3Equiv x i = x i`. Mark it `@[simp]` after checking that it does not conflict with `PiLp.continuousLinearEquiv_apply`. Add `l2Vec3Equiv_l2BasisVec : l2Vec3Equiv (l2BasisVec i) = CKN.basisVec i`, the fact proved inline at lines 186–188. That fact is also closely related to the public `l2Vec3Equiv_symm_basisVec` in `JSpaceFourierPotentialBase`. Then drop `l2Vec3Equiv` from the simp sets.

Benefit: The definition no longer has to be unfolded by name. The inline `show ... by ext j; simp [...]` in `weakTestGradientSchwartz_apply` becomes a rewrite with a named lemma that other files can also use.

Source evidence:

- `weakTestGradientSchwartz_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: simp [l2BasisVec, l2Vec3Equiv, CKN.basisVec, Pi.single_apply]]
- `l2Vec3Equiv_symm_basisVec` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/JSpaceFourierPotentialBase.lean`: simp [l2BasisVec3, l2Vec3Equiv, basisVec]

### fragile-proofs: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L140-L142)

Declaration: `DFinsupp.card_pi`

`DFinsupp.prod` expects `g : ∀ i, β i → γ`. Here `fun i ↦ #(f i)` has type `ℕ` in the body, so Lean elaborates it through a `NatCast (Finset (α i) → ℕ)` coercion (the Pi natCast instance). The statement therefore means `(↑#(f i) : Finset (α i) → ℕ) (f i)`. The proof only works by undoing this coercion with `Pi.natCast_apply, Nat.cast_id`. A routine change to the elaboration, coercion instances or the simp-set of those lemmas would break both the statement and the proof. It also hides that the intended statement is `∏ i ∈ f.support, #(f i)`.

Proposed change:

State the lemma with an explicit function, `f.prod fun i s ↦ #s`, or directly as `∏ i ∈ f.support, #(f i)`. Then the proof is `card_dfinsupp _ _`, or `rw [pi, card_dfinsupp]` followed by `rfl`. This removes the dependence on `Pi.natCast_apply` and `Nat.cast_id`.

Benefit: The statement says what it means. The proof no longer depends on an incidental coercion or on simp lemmas that undo it. Users can rewrite with `card_pi` without a stray cast appearing in the goal.

Source evidence:

- `DFinsupp.prod` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/BigOperators.lean`: (g : ∀ i, β i → γ) : γ :=
  ∏ i ∈ f.support, g i (f i)
- `Finset.card_dfinsupp` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: #(s.dfinsupp t) = ∏ i ∈ s, #(t i)

### fragile-proofs: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L48-L59)

Declaration: `Finset.mem_dfinsupp_iff`

The reverse direction uses a bare `dsimp` to expose the internal definition of `DFinsupp.mk`, which it unfolds to an `ite` on membership in `s`. It then closes the goal with `ite_eq_left_iff` against that exact shape. If `DFinsupp.mk` or its coercion simp-normal form changes (for example a different decidability instance or a `dite`), `dsimp` and the `exact` break. The forward direction already uses the public lemmas `mk_of_mem` and `support_mk_subset` instead.

Proposed change:

Prove equality pointwise with the public API. After `ext i`, `by_cases hi : i ∈ s`. Use `mk_of_mem hi` in the positive case. In the negative case use `mk_of_notMem` (if available, otherwise `notMem_support_iff` with `support_mk_subset`) and `notMem_support_iff.1 (mt h.1 hi)`. This replaces `dsimp` and the `ite` match with named lemmas.

Benefit: The proof depends on the stable `mk_of_mem` / `mk_of_notMem` interface instead of the unfolded `mk` body. It also mirrors the forward direction, so a reader sees one consistent mechanism.

Source evidence:

- `Finset.mem_dfinsupp_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`:     exact mk_of_mem hi

### fragile-proofs: [Mathlib/Topology/Category/Profinite/EffectiveEpi.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L86-L90)

Declaration: `Profinite.effectiveEpiFamily_tfae`

`erw` rewrites the goal `(∀ b : B, ∃ a x, π a x = b) ↔ EffectiveEpiFamily X π` using an iff about `profiniteToCompHaus.obj (X a)` and `profiniteToCompHaus.map (π a)`. The pattern only matches the goal up to unfolding of the functor's `obj`, `map` and coercions. Ordinary `rw` cannot see this match, so the proof depends on `erw`'s transparency for finding the rewrite site. A small change to how `profiniteToCompHaus` or the `Profinite` and `CompHaus` coercions reduce could make the rewrite fail to find its pattern. The step after the rewrite also relies on the exact shape of the rewritten goal.

Proposed change:

Drop `erw` and compose the iffs explicitly. For example, replace lines 86–90 with `tfae_have 3 ↔ 1 := by`, then `refine ((CompHaus.effectiveEpiFamily_tfae (fun a ↦ profiniteToCompHaus.obj (X a)) (fun a ↦ profiniteToCompHaus.map (π a))).out 3 1).trans ⟨fun h ↦ profiniteToCompHaus.finite_effectiveEpiFamily_of_map _ _ h, fun _ ↦ inferInstance⟩`. The defeq check between the CompHaus statement and the Profinite statement then happens once, at `refine`'s default transparency, with explicit arguments. This has not been compiled.

Benefit: The unification no longer depends on `erw` locating a rewrite site. Any failure appears as a single type mismatch at `refine`. The mathematical structure is also clearer: it is the CompHaus iff composed with 'effective epi family reflects and preserves under `profiniteToCompHaus`'.

Source evidence:

- `CompHaus.effectiveEpiFamily_tfae` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/CompHaus/EffectiveEpi.lean`:     , ∀ b : B, ∃ (a : α) (x : X a), π a x = b
- `Profinite.effectiveEpiFamily_tfae` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean`: exact ⟨fun h ↦ profiniteToCompHaus.finite_effectiveEpiFamily_of_map _ _ h,

### fragile-proofs: [Mathlib/Topology/Category/Profinite/EffectiveEpi.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L82-L84)

Declaration: `Profinite.effectiveEpiFamily_tfae`

This step is a direct term-level argument: `Epi (Sigma.desc π)` gives `EffectiveEpi (Sigma.desc π)`, which gives `EffectiveEpiFamily X π`. It is proved with `simpa` using a reversed lemma and an `Iff` taken from a TFAE. Whether it closes depends on the simp-set. A new simp lemma about `Epi (Sigma.desc _)` or `EffectiveEpi`, or a change to how a reversed iff is oriented, could make `simpa` rewrite the goal or hypothesis differently, or loop. The `.out 1 2` hypothesis is used as an oriented rewrite rule instead of being applied.

Proposed change:

Replace the `simpa` with an explicit term: `| h => (effectiveEpi_desc_iff_effectiveEpiFamily X π).mp (((effectiveEpi_tfae (Sigma.desc π)).out 2 1).mp h)`. The `.out 2 1` goes from `Epi` to `EffectiveEpi`; the original `.out 1 2` goes the other way. This has not been compiled.

Benefit: The two cited lemmas are applied directly, so the proof no longer depends on simp-set behaviour. Both steps appear in the term, and any breakage becomes a clear type error.

Source evidence:

- `CategoryTheory.effectiveEpi_desc_iff_effectiveEpiFamily` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/CategoryTheory/EffectiveEpi/Extensive.lean`: EffectiveEpi (Sigma.desc π) ↔ EffectiveEpiFamily X π
- `List.TFAE.out` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/List/TFAE.lean`: theorem TFAE.out {l} (h : TFAE l) (i j : Nat) {a b}

### fragile-proofs: [TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean#L51-L59)

Declaration: `TauCeti.gradedIdempotentHeadBasis`

The two side-condition proofs use `classical` followed by `simpa`. The cited lemma already gives exactly `... = if j = i then 1 else 0`. The goal is instead `(headFamily he₀ i).obj.smulGradedDimension (e j) = 0` (or `= 1`), where `headFamily` is a private abbrev. The proof therefore relies on the default simp set to unfold the abbrev and the FullSubcategory projection. It also relies on simp to reduce the `if` with the supplied `hji`, and to rewrite the goal and the hypothesis into the same normal form. A routine change to simp lemmas for `smulGradedDimension`, `Pairwise`, or `FullSubcategory.obj` could leave the goal and the hypothesis in different forms. The `classical` call is needed only to supply the lemma's `[DecidableEq I]` argument. It gives no mathematical content, and the `if` condition is then stated with a classical instance.

Proposed change:

Drop `simpa` and use the lemma's own statement as a term, so the `if` is reduced by the explicit lemmas `if_neg hji` and `if_pos rfl`. For example, the first obligation could be `fun j i hji => by classical; exact (smulGradedDimension_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan j i (hne i)).trans (if_neg hji)`, and the second `... .trans (if_pos rfl)`. This relies on `headFamily i`.obj being definitionally `gradedPositiveMulQuotient 𝒜 (he₀ i)`, which holds for the abbrev. Alternatively, `rw [lemma, if_neg hji]` can be used.

Benefit: The proof depends only on the public statement of `smulGradedDimension_gradedIdempotentHead` and on `if_neg`/`if_pos`. It no longer depends on how simp normalizes the goal. A reader can also see that the hypotheses are just the Kronecker-delta statement specialized to `j ≠ i` and `j = i`.

Source evidence:

- `TauCeti.smulGradedDimension_gradedIdempotentHead` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Category/GradedModuleCat/Idempotent/Head.lean`: (gradedPositiveMulQuotient 𝒜 (he₀ i)).smulGradedDimension (e j) = if j = i then 1 else 0
- `TauCeti.gradedSimpleClassBasis` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/SimpleBasis.lean`: (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)

### fragile-proofs: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L386-L399)

Declaration: `TauCeti.ReducedTensorWords.isCoderivation_coderiv`

The ending relies on goal shape and traversal order. `rw [add_comm]` has no explicit arguments, so it rewrites the first `_ + _` instance it finds. That must be the top-level sum of the left side, and the two summands must then line up with the `congr 1` bullets in the order given. The bullets also depend on the exact nesting of the `Finset.sum`s, through `Eq.trans (Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm) Finset.sum_comm` and a bare `rw [Finset.sum_comm]`. Reordering the summands in `hLHS` or `hRHS`, or a change in which instance `rw` finds first, would break the proof. The error would show up in an unrelated bullet.

Proposed change:

Name the four sums as local `have`s, or state `hLHS` and `hRHS` so the summands are already in matching order. Then close with an explicit `rw [hLHS, hRHS, add_comm (a := _) (b := _)]` or `exact (add_comm _ _).trans (congrArg₂ (· + ·) h₁ h₂)`. The two component equalities `h₁` and `h₂` would be proved separately, each with its own `Finset.sum_comm` or `sum_range_triangle` step and explicit arguments. This removes dependence on `rw` choosing the right instance and on `congr 1` splitting the goal as expected.

Benefit: The two halves of the co-Leibniz identity become independently checkable steps. A reindexing or reordering change then fails locally with a readable goal instead of cascading through positional bullets.

Source evidence:

- `TauCeti.ReducedTensorWords.isCoderivation_coderiv` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean`: rw [hLHS, hRHS, add_comm]
  congr 1
  · exact Eq.trans (Finset.sum_congr rfl fun p _ ↦ Finset.sum_comm) Finset.sum_comm

### fragile-proofs: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L129-L147)

Declaration: `TauCeti.ReducedTensorWords.coderivSummand_tprod`

After a large `simp only` set, the proof expects a goal of a specific shape. That includes `Function.comp_apply` still being present, `Fin.append` appearing exactly twice nested, and the results being `dite`s over the same conditions. It then closes the goal with a positional sequence of `rw [dite_eq_left h₁, dite_eq_left h₁]` and `rw [dite_eq_right h₁, dite_eq_right h₁, append_eq_dite]`. Any routine change would break this: a different `simp` normal form for `TensorPower.cast_tprod` or `gMul_def`, a change to how `splice` or `subword` are defined, or a different simp-set normalisation of `Fin.val_cast`. The repeated identical rewrites also depend on `rw` instantiating the motive at the right occurrence each time.

Proposed change:

Prove the index equality using the public `Fin.append` interface instead of the private `append_eq_dite` and `dite` rewrites. For example, do `induction`/`Fin.addCases` on the index, or case on `i.1 < p` and `i.1 = p`. Use `Fin.append_left` and `Fin.append_right`, which are stated for `Fin.castAdd` and `Fin.natAdd`, to state per-case lemmas such as `∀ i, i.1 < p → _ = x _`. Alternatively, factor the pointwise statement out as a standalone lemma about `Fin.append (Fin.append u v) w`. The main proof would then only need `of_tprod_congr` plus that lemma, rather than sequences of `rw [dite_eq_*]` that rely on the goal's exact syntactic form.

Benefit: The pointwise index computation would no longer depend on the exact `dite` structure produced by an unfolded `Fin.append`. A change in simp normal forms would only affect the simp call, not a dozen following rewrites.

Source evidence:

- `TauCeti.ReducedTensorWords.append_eq_dite` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean`: Fin.append u v i = if hi : i.1 < k then u ⟨i.1, hi⟩ else v ⟨i.1 - k, by omega⟩
- `Fin.append_left` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Data/Fin/Tuple/Basic.lean`: theorem append_left (u : Fin m → α) (v : Fin n → α) (i : Fin m)

### fragile-proofs: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L191-L248)

Declaration: `zero_mem_convexHull_of_best_approx (h_active branches)`

The ε witness is written as `M / (-∑ i ∈ S, Λ (Function.update 0 i 1))` in the first branch and `M / (∑ i ∈ S, Λ (Function.update 0 i 1))` in the second. Each `exact ⟨…⟩` therefore only typechecks if two stacked `simp_all` calls leave the goal in exactly one shape. The shape depends on the simp-set order, on `simp_all` rewriting the hypotheses `h_additiveFunction_a_pos` and `h_additiveFunction_a_neg` (including `a`, which is a `set` variable), and on the lemmas `map_neg`, `Left.neg_neg_iff` and `abs_eq_self`. A routine simp-lemma or normal-form change in Mathlib, or a small edit to the `hΛ_gen` hypotheses, would change the goal. The explicit witness and the `nlinarith` calls would then fail. The proof never states the actual identity it needs, `additiveFunction (fun i => ε' * a i) S = ε' * additiveFunction a S`.

Proposed change:

Prove once a local lemma `additiveFunction (fun i => c * a i) S = c * additiveFunction a S` using `Finset.mul_sum`. Then do not use `simp_all`. State the witness in terms of the named quantity `s := additiveFunction a S`, for example `ε := M / s` in the positive case (with `hs : 0 < s`) and `M / (-s)` in the negative case. For 0 < ε' < ε the goal reduces to `|M - ε' * s| < M` or `|-M - ε' * s| < M`. Close it with `abs_lt` and `nlinarith` or `mul_lt_mul_of_pos_left`, with all hypotheses passed explicitly and no `simp_all`.

Benefit: The proof would no longer depend on the exact normal form simp produces. A reader could see the one-line reason it works: ε·s is strictly between 0 and M.

Source evidence:

- `additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: fun A => ∑ i ∈ A, a i

### fragile-proofs: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L136-L137)

Declaration: `zero_mem_convexHull_of_best_approx (Hahn–Banach application)`

The theorem is introduced with `@`, so the proof depends on the number and order of implicit and instance arguments, and then `convert` closes the goal up to defeq. The statement is `∃ (f : StrongDual ℝ E) (u : ℝ), (∀ a ∈ s, f a < u) ∧ u < f x`. The goal here is already that statement with `s := convexHull …`, `x := 0` and `StrongDual ℝ (U → ℝ)` written as `(U → ℝ) →L[ℝ] ℝ`. Adding an implicit argument to the theorem would break the `@` form. `convert` can also silently produce unintended side goals, or fail unpredictably. The same lemma name exists in the `RCLike` namespace with a different statement (`re (f a) < u`), so a change to opened namespaces could alter what the bare name resolves to.

Proposed change:

Apply the theorem directly with explicit arguments and no `@` or `convert`: `obtain ⟨Λ, u, hΛ, hu⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull ℝ (activeGenerators_finite f M)) h_contra`. Use `(x := 0)` if unification needs help. The `h_closed_convex` conjunction can then be dropped.

Benefit: The proof depends only on the lemma's explicit hypotheses. It is shorter, and it does not rely on `convert` or on the argument order of the lemma.

Source evidence:

- `geometric_hahn_banach_closed_point` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/LocallyConvex/Separation.lean`: theorem geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (disj : x ∉ s) :

### fragile-proofs: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L394-L435)

Declaration: `dual_cert_from_convexHull (h_sum_eq block)`

This proof depends on how many side goals remain, and in what order, after a chain of `simp only [...]`, `rw [Finset.sum_eq_single S, Finset.sum_eq_zero] <;> simp +contextual only [...]` and `simp_all`. The trailing bullets (`· intro T hT₁ hT₂ …`, `· aesop`) are matched to these goals by position. In the second branch the bullet order is swapped (`· aesop` first, then `· intro T …`), which shows the order is incidental. The proof also relies on `simp_all` rewriting every hypothesis in context, on `split_ifs at this <;> norm_num at this`, and on `Set.mem_ofPred_eq`, which is an implementation-level lemma name. If a simp lemma changes, or `rw` generates its side goals in a different order, the bullets fail or `aesop` is applied to the wrong goal.

Proposed change:

State the needed fact as a standalone lemma with explicit hypotheses. It would say that for `v = S.indicator'` or `v = -S.indicator'`, the sum `∑ T ∈ univ.filter (f · = M), if v = T.indicator' then v else 0` equals `v`. Prove it with `Finset.sum_eq_single_of_mem` and `indicator'_injective.eq_iff`, and use `indicator'_injective` to show `S.indicator' ≠ -T.indicator'` for the non-matching terms, so each side goal is supplied by name. Alternatively, rewrite `lam_pos`/`lam_neg` through `Finset.sum_comm` and `Finset.sum_ite_eq` so that no position-dependent side-goal bullets are needed.

Benefit: The two near-duplicate branches would share a named lemma and no longer depend on side-goal order or on `simp_all` normal forms. A routine `simp` change would not silently break the proof.

Source evidence:

- `indicator'_injective` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: lemma indicator'_injective : Function.Injective (Finset.indicator' : Finset U → (U → ℝ)) := by

### fragile-proofs: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L314-L376)

Declaration: `dual_cert_from_convexHull (lam_pos/lam_neg construction)`

The four goals produced by `refine … <;> simp_all +decide only [...]` are closed by position-dependent bullets (`intro S; split_ifs <;> simp +decide [*, le_of_lt]`, `grind`, then `convert hw_zero.1 using 1`, which depends on the exact `simp_all` output). The `convert … using 1` and the following `rw [← Finset.sum_subset (show … ⊆ c from ?_)]` expect a specific sum shape. The later steps use unlabelled `grind` calls and `simp_all` on the whole context, plus `contrapose! hM_pos` and `rw [show S₂ = ∅ by ext x; aesop] at hS₂`. These need the hypotheses to have exactly the shape `simp_all` leaves, with the names `hS₂` and `hM_pos` surviving. The goals are also ordered `?_` (subset), then three more bullets, so adding an extra hypothesis or changing the sum simp lemmas reorders or breaks them. The destructured names `hw_pos_def` and `hw_neg_def` are also misleading: `hw_neg_def.2.2` is accessed positionally to mean the last conjunct.

Proposed change:

Name the conjuncts in the `obtain` pattern (`⟨lam_pos, lam_neg, h_nonneg, h_support, h_sum, h_zero⟩`). Prove each of the four properties as a separate `have` or lemma with an explicit statement, rather than through `<;> simp_all`. Use the explicit rewriting lemmas the proof already touches (`Finset.sum_comm`, `sum_filter`, `Finset.sum_image`, `indicator'_injective`) instead of `grind` or `simp_all` on the whole context. Keep `grind` only for closing small arithmetic goals, with the needed hypotheses named.

Benefit: The proof would survive routine changes to simp normal forms or to `grind`'s behaviour. Each step would state what it proves.

Source evidence:

- `dual_cert_from_convexHull` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: replace hw_neg_def := congr_fun hw_neg_def.2.2 i

### fragile-proofs: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L174-L178)

Declaration: `zero_mem_convexHull_of_best_approx (h_inactive continuity step)`

This continuity argument uses the aesop-based `continuity` tactic. Its own docstring says `fun_prop` is a usually more powerful alternative. `continuity` searches under a rule set and can break when the goal's shape changes. Here the goal is the function after `simp +decide only [additiveFunction]` has unfolded the sum, so the proof depends on that exact unfolded term. The limit value is closed by `simp +decide`, which depends on how simp rewrites `|f S - ∑ i ∈ S, 0 * a i|` to `|f S|`.

Proposed change:

Replace `by continuity` with `by fun_prop`. For the whole step, use a continuity argument stated before unfolding: `ε' ↦ |f S - ε' * ∑ i ∈ S, a i|` is continuous (via `fun_prop` or `Continuous.abs`), and `Continuous.continuousAt` gives the tendsto at 0. Compute the limit with `zero_mul` and `sub_zero` explicitly.

Benefit: The proof would rely on the more robust `fun_prop` or on explicit continuity lemmas. It would no longer depend on aesop's search or on the simp-unfolded form of `additiveFunction`.

Source evidence:

- `continuity tactic docstring` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Tactic/Continuity.lean`: `fun_prop` is a (usually more powerful) alternative to `continuity`.

### fragile-proofs: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L299-L300)

Declaration: `realPart_isWeakDivFree_of_fourierOrthogonal (hpoint)`

The `simp only` set reaches inside how `realPartValue` is built. It unfolds `realPartValue` and `realPartValueLinear`, then peels the `mkContinuous` wrapper and the `LinearMap.mk`/`AddHom.mk` structure projections to reach the coordinate `(z i).re`. The proof therefore depends on `realPartValue` being a `mkContinuous` of a hand-built `LinearMap` with `toFun z := WithLp.toLp 2 (fun i => (z i).re)`. Changing how the continuous linear map is built would break it. The same unfolding is repeated in ForcePressureOrthogonality.lean, FourierMildInitialTrace.lean and ForcedRegMomentumSlicePressure.lean. FourierRealification.lean provides no public apply lemma for `realPartValue`.

Proposed change:

Next to the definition of `realPartValue`, add a `@[simp]` lemma such as `realPartValue_apply (z : ComplexVec3) (i : Fin 3) : realPartValue z i = (z i).re`, proved once by `rfl` or `simp [realPartValue, realPartValueLinear]`. Then use it in `hpoint` by replacing the unfolding and structure-projection lemmas with `realPartValue_apply`. The other call sites that unfold `realPartValueLinear` can use it too.

Benefit: Changes to how `realPartValue` is constructed would only touch one lemma, not every downstream `simp` call. The proof would also show the mathematical step (real part of the coordinate) instead of the `mkContinuous` plumbing.

Source evidence:

- `realPartValue` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierRealification.lean`: realPartValueLinear.mkContinuous 1 (by
- `realPartValueLinear` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierRealification.lean`: toFun z := WithLp.toLp 2 (fun i => (z i).re)
- `forcePressure_inner_realPartValue` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/ForcePressureOrthogonality.lean`: simp [realPartValue, realPartValueLinear, complexifyValue, complexifyValueLinear,

### fragile-proofs: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L173-L189)

Declaration: `weakTestGradientSchwartz_apply`

This proof is a long sequence of `change` steps. They rely on definitional unfolding of `weakTestGradientSchwartz`, `fderivCLM`, `postcompCLM`, `compCLMOfContinuousLinearEquiv`, `toSchwartzMap` and `ψ.toFun`, with a closing bare `rfl`. The `change` terms spell out the elaborated form of the coercions (`fun z => weakTestSchwartz z`, `ψ.toFun ∘ l2Vec3Equiv`, `(l2Vec3Equiv : L2Vec3 → Vec3)`). They will stop matching if any of these definitions is made irreducible or restructured, for example if the Schwartz-map coercion or `toSchwartzMap` is reworked. A later `Complex.ofRealCLM` or coercion form change in Mathlib would also break them. Mathlib already has public apply lemmas for each wrapper, so the proof does not need to depend on how the wrappers are defined.

Proposed change:

Rewrite with the public apply lemmas instead of `change`. First rewrite `SchwartzMap.postcompCLM_apply` and `SchwartzMap.fderivCLM_apply` to get `gradientOfCovector (fderiv ℝ (⇑(weakTestComplexSchwartz ψ)) x) i`. Then use the `@[simp]` lemma `SchwartzMap.compCLMOfContinuousLinearEquiv_apply` to evaluate `weakTestSchwartz ψ z` as `ψ (l2Vec3Equiv z)`. Finish with the chain rule: `HasFDerivAt.comp` with `l2Vec3Equiv.hasFDerivAt` and `Complex.ofRealCLM.hasFDerivAt`. It would also help to add small `@[simp]` apply lemmas for `weakTestSourceSchwartz`, `weakTestSchwartz` and `weakTestComplexSchwartz`, so the unfolding happens in one place.

Benefit: The proof would depend on the stated API of Schwartz maps rather than on how the intermediate maps were built. A routine refactor would then not require re-deriving which `change` form to write, and the chain-rule reasoning would be visible.

Source evidence:

- `SchwartzMap.postcompCLM_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean`: theorem postcompCLM_apply (L : F →L[𝕜] G) (f : 𝓢(E, F)) (x : E) : f.postcompCLM L x = L (f x)
- `SchwartzMap.fderivCLM_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Distribution/SchwartzSpace/Deriv.lean`: theorem fderivCLM_apply (f : 𝓢(E, F)) (x : E) : fderivCLM 𝕜 E F f x = fderiv ℝ f x
- `SchwartzMap.compCLMOfContinuousLinearEquiv_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean`: @[simp] lemma compCLMOfContinuousLinearEquiv_apply (g : D ≃L[ℝ] E) (f : 𝓢(E, F)) :

### fragile-proofs: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L320-L325)

Declaration: `realPart_isWeakDivFree_of_fourierOrthogonal (pointwise comparison step)`

The step restates `hp` with a `change ... at hp` that exposes the raw `.ofLp` projection. It then closes with `simpa [F, realPartVectorL2Representative, l2Vec3Equiv] using hp`, whose simp set unfolds the definition of `l2Vec3Equiv`. This depends on the exact elaborated shape of the `PiLp` coercion and on the unfolding of `l2Vec3Equiv` (`PiLp.continuousLinearEquiv`). The name `ofLp` and the shape of the coercion are a `WithLp` implementation detail that has changed before. The proof would break if `WithLp` coercions were redesigned or `l2Vec3Equiv` were defined differently. `hpoint` also states the conclusion in terms of `realPartValue (v x) i` and `l2Vec3Equiv x`, so a lemma about `realPartVectorL2Representative` coordinates would remove the mismatch.

Proposed change:

Add a small public lemma, for example `realPartVectorL2Representative_apply (v) (x : Vec3) (i : Fin 3) : realPartVectorL2Representative v x i = realPartValue (v (WithLp.toLp 2 x)) i`. A similar lemma for `l2Vec3Equiv` would also be needed: `l2Vec3Equiv x i = x.ofLp i`, a `PiLp.continuousLinearEquiv` apply lemma. Prove both once with `rfl` or `simp`, then close this step with `simpa [realPartVectorL2Representative_apply] using hpoint (WithLp.toLp 2 x)` without the `change`.

Benefit: The coordinate-level unfolding is isolated in two named lemmas. The main calculation no longer depends on the internal `ofLp` form or on unfolding the equivalence `l2Vec3Equiv`.

Source evidence:

- `l2Vec3Equiv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
- `realPartVectorL2Representative` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: fun x => l2Vec3Equiv
    (realPartValue (v (WithLp.toLp 2 x)))

### repeated-proof-machinery: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L115-L123)

Declaration: `DFinsupp.support_rangeIcc_subset (also repeated in DFinsupp.rangeIcc)`

`rangeIcc`'s `support'` proof (lines 100-109) and `support_rangeIcc_subset` both prove the same fact. If `i` lies outside the supports of `f` and `g`, then `f i = 0` and `g i = 0`, so `Icc (f i) (g i) = {0}`. The first proof does this with multiset membership (`Multiset.notMem_mono`, `Multiset.le_add_right`, `simp_rw [hf, hg]`). The second does it with `Finset` supports. `mem_dfinsupp_iff_of_support_subset` (lines 70-72) repeats the same reasoning for a general `t`, using `zero_mem_zero`. The Finsupp analogue instead packages this as a single `Icc_eq_singleton_iff` step.

Proposed change:

Add a small lemma before `rangeIcc`, with `Zero` and `PartialOrder` on `α`:
`lemma Icc_zero_zero_eq_singleton : Icc (0 : α) 0 = {0} := Icc_self _`
Without `Zero`, state it as `f i = 0 → g i = 0 → Icc (f i) (g i) = {0}`.
Or state the obligation once on the `Prop` level:
`lemma Icc_eq_zero_of_apply_eq_zero {a b : α i} (ha : a = 0) (hb : b = 0) : Icc a b = 0`, where `0` is the `Finset` zero, i.e. `{0}`.
Then:
- In `support_rangeIcc_subset`, use `notMem_support_iff.2 (Icc_eq_zero_of_apply_eq_zero (notMem_support_iff.1 …) (notMem_support_iff.1 …))` for the goal `(f.rangeIcc g) i = 0`.
- In `rangeIcc`, the `support'` obligation reduces to deriving `f i = 0` and `g i = 0` and applying the same lemma.
- Lines 70-72 can use the same lemma in the `Finset` zero-equals-singleton form instead of `zero_mem_zero`.
Alternatively, define `rangeIcc`'s `support'` from `Icc_eq_singleton_iff`, as in `Finsupp.rangeIcc`.

Benefit: The "outside the support, the interval is `{0}`" argument is stated once and named. `rangeIcc` and `support_rangeIcc_subset` then no longer re-derive the `Icc_self` step, and `mem_dfinsupp_iff_of_support_subset` can reuse it. This also aligns the DFinsupp file with the shorter Finsupp proof.

Source evidence:

- `DFinsupp.rangeIcc` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: simp_rw [hf, hg]
        exact Icc_self _⟩
- `Finset.mem_dfinsupp_iff_of_support_subset` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: rw [notMem_support_iff.1 (mt h.1 hi), notMem_support_iff.1 (notMem_mono ht hi)]
- `Finsupp.rangeIcc` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/Finsupp/Interval.lean`: exact Icc_eq_singleton_iff.symm

### repeated-proof-machinery: [Mathlib/Topology/Category/Profinite/EffectiveEpi.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L74-L91)

Declaration: `Profinite.effectiveEpiFamily_tfae`

The whole proof of this theorem, and of effectiveEpiFamily_of_jointly_surjective, is repeated almost verbatim in Stonean.effectiveEpiFamily_tfae. The 2→1 step via `effectiveEpi_desc_iff_effectiveEpiFamily`, the 1→2 step and the 3↔1 transfer through CompHaus are identical. Only the functor (`profiniteToCompHaus` vs `Stonean.toCompHaus`) and the category name differ. The argument uses just three facts: a functor F : C ⥤ CompHaus that preserves and reflects finite effective epi families, a CompHaus TFAE, and the fact that F commutes with the jointly-surjective condition. It is not specific to Profinite or Stonean.

Proposed change:

Add a helper, e.g. in the CompHaus/EffectiveEpi file or a CompHausLike one: for `F : C ⥤ CompHaus` with `[F.PreservesFiniteEffectiveEpiFamilies] [F.ReflectsFiniteEffectiveEpiFamilies]` and `F` faithful and fully faithful on points (the underlying-function compatibility), state `(∀ b : B, ∃ a x, π a x = b) ↔ EffectiveEpiFamily X π` for finite `α`. Equivalently, state `Finite α → (EffectiveEpiFamily X π ↔ EffectiveEpiFamily (F.obj ∘ X) (F.map ∘ π))` plus the CompHaus TFAE. Then both Profinite and Stonean prove `3 ↔ 1` as `helper profiniteToCompHaus X π` and `helper Stonean.toCompHaus X π`. This removes the duplicated `erw` and `finite_effectiveEpiFamily_of_map` block, about 15 lines in each file. It also lets the `erw` be confined to one place.

Benefit: One maintained proof of the finite-family criterion for concrete full subcategories of CompHaus, instead of two copies that must be fixed in step. A reader sees that the criterion is a consequence of preserving and reflecting finite effective epi families, not a coincidence of the two files.

Source evidence:

- `Stonean.effectiveEpiFamily_tfae` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/Stonean/EffectiveEpi.lean`: erw [((CompHaus.effectiveEpiFamily_tfae
      (fun a ↦ Stonean.toCompHaus.obj (X a)) (fun a ↦ Stonean.toCompHaus.map (π a))).out 3 1 :)]
    exact ⟨fun h ↦ Stonean.toCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
- `Stonean.effectiveEpiFamily_tfae` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/Stonean/EffectiveEpi.lean`: simpa [← effectiveEpi_desc_iff_effectiveEpiFamily, (effectiveEpi_tfae (Sigma.desc π)).out 1 2]

### repeated-proof-machinery: [Mathlib/Topology/Category/Profinite/EffectiveEpi.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L35-L53)

Declaration: `Profinite.effectiveEpi_tfae and the PreservesEffectiveEpis / ReflectsEffectiveEpis instances for profiniteToCompHaus`

The effective-epi-iff-surjective TFAE and the two instances saying that the inclusion into CompHaus preserves and reflects effective epis are repeated for Stonean (and CompHaus) with the same shape. Each instance just chains two `.out 1 3` conversions through surjectivity. Each category re-proves `effectiveEpi_tfae` with the same three-line body, and re-writes the same preserves/reflects pair.

Proposed change:

Add a lemma such as `effectiveEpi_iff_surjective` for a concrete category whose forgetful functor to CompHaus is fully faithful and that has an `effectiveEpiStruct`. Alternatively, derive preservation and reflection once from the equivalence of both sides with surjectivity. It would take a functor `F : C ⥤ CompHaus` with `F.map f` having the same underlying function as `f`, and give `[F.PreservesEffectiveEpis] [F.ReflectsEffectiveEpis]` for the inclusion functors. Profinite and Stonean would then reduce to `inferInstance` or a one-line application.

Benefit: This removes the duplicated bridging proofs in the Profinite and Stonean files. Adding another CompHausLike subcategory would then take one line.

Source evidence:

- `Stonean.instReflectsEffectiveEpisToCompHaus (instance : Stonean.toCompHaus.ReflectsEffectiveEpis)` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/Stonean/EffectiveEpi.lean`: ((Stonean.effectiveEpi_tfae f).out 1 3).mpr
      (((CompHaus.effectiveEpi_tfae (Stonean.toCompHaus.map f)).out 1 3).mp h)
- `CompHaus.effectiveEpi_tfae` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/CompHaus/EffectiveEpi.lean`: tfae_have 3 → 1 := fun hπ ↦ ⟨⟨effectiveEpiStruct π hπ⟩⟩

### repeated-proof-machinery: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L346-L399)

Declaration: `TauCeti.ReducedTensorWords.isCoderivation_coderiv`

The ~55-line co-Leibniz verification is repeated almost line for line in `isGradedCoderivation_gradedCoderiv`. It has the same `hLHS`, `hdelta` and `hRHS` expansions via `deconcatenation_splice` and `deconcatenation_subword`. It uses the same `congr 1` plus `sum_congr` plumbing, and the same `sum_tmul_splice_eq_zero` / `sum_range_triangle` triangle reindexing followed by `Finset.sum_comm` and `c + (p - c) = p`. The graded proof differs only in that the tuple being spliced is `twistedTuple G q x 0 p` (or `twistedTuple G q x c p`) rather than `x`. The combinatorial core (cut position, block position, block length) is proved twice, so any fix to the reindexing must be made in two places.

Proposed change:

Factor out a lemma stated for a family of tuples `y : ℕ → Fin n → M` and a family of letters `e : ℕ → ℕ → M`. It would say that `deconcatenation` of `∑ p ∈ range n, ∑ d ∈ range (n+1), splice R (y p) 0 n p d (e p d)` equals the sum over cut `c` and block `p` of the left-collapsed and right-collapsed terms, with the right half expressed through the `Σ_{c ≤ p}` triangle-reindexed form. Alternatively, state the purely combinatorial reindexing step (the `hA1`/`hA2` argument) as a lemma about an arbitrary `g : ℕ → ℕ → ℕ → TensorProduct ..` vanishing off the triangle. `isCoderivation_coderiv` would instantiate it with `y := fun _ => x`, and the graded version with `y := fun p => twistedTuple G q x 0 p`. That leaves only the congruence facts about `twistedTuple` in the graded file.

Benefit: This removes roughly 50 duplicated lines from each of the two proofs. The shared lemma is a natural statement: the deconcatenation of a Taylor expansion splits into a left-collapsed part and a right-collapsed part. Future variants (other twists) would not need to copy the proof.

Source evidence:

- `TauCeti.ReducedTensorWords.isGradedCoderivation_gradedCoderiv` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean`: have hdelta : deconcatenation R M (subword R x 0 n.1) =
      ∑ c ∈ Finset.range n.1, subword R x 0 c ⊗ₜ[R] subword R x c (n.1 - c) := by
- `TauCeti.ReducedTensorWords.isGradedCoderivation_gradedCoderiv` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean`: rw [(sum_range_triangle n.1 _ hg).symm]

### repeated-proof-machinery: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L438-L451)

Declaration: `TauCeti.ReducedTensorWords.letter_comp_coderiv`

The proof isolates the single surviving summand `(p, d) = (0, n)` of the Taylor expansion with two nested `Finset.sum_eq_single` calls. It kills the other terms using `letter_splice_eq_zero_of_not_whole` and evaluates the survivor with `letter_splice_self`. `letter_comp_gradedCoderiv` repeats the same skeleton, with `x` replaced by `twistedTuple G q x 0 p`. The `absurd`/membership side goals and the `(by omega)` arithmetic are duplicated.

Proposed change:

Add a lemma such as `letter_sum_splice_whole`. For `0 < n`, a family `y : ℕ → Fin n → M` and `e : ℕ → ℕ → M`, it would state `letter R M (∑ p ∈ Finset.range n, ∑ d ∈ Finset.range (n+1), splice R (y p) 0 n p d (e p d)) = e 0 n`. It is proved once with the two `sum_eq_single` steps. `letter_comp_coderiv` would then be `linearMap_ext` followed by `coderiv_subword` and this lemma with `y := fun _ => x`. `letter_comp_gradedCoderiv` would use `y := fun p => twistedTuple G q x 0 p` and then rewrite `twistedTuple G q x 0 0 = x`, if that is available.

Benefit: Both Taylor-component proofs shrink to a few lines. The 'only the whole-word collapse contributes a letter' fact becomes a named, reusable statement. The index and membership bookkeeping, which is the error-prone part, lives in one place.

Source evidence:

- `TauCeti.ReducedTensorWords.letter_comp_gradedCoderiv` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean`: refine (Finset.sum_eq_single 0 ?_ ?_).trans ?_
- `TauCeti.ReducedTensorWords.letter_comp_gradedCoderiv` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoderivation.lean`: letter_splice_eq_zero_of_not_whole R (twistedTuple G q x 0 p) _ (by omega)

### repeated-proof-machinery: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L171-L248)

Declaration: `zero_mem_convexHull_of_best_approx (h_inactive / h_active inside the ε-selection)`

The proof shows that a small ε > 0 keeps |f S − ε·a(S)| < M for each S. It does this three times with the same shape: `h_inactive`, and the `f S = M` and `f S = -M` branches of `h_active`. The two active branches are mirror images. Each runs two long `simp_all +decide only [...]` calls with almost the same lemma lists (they differ only in `abs_neg` and `abs_eq_self`). Each then gives an explicit witness `M / (∓∑ Λ …)` and closes two `nlinarith` goals. All of this is the one-dimensional fact that for x, y with |x| = M and x·y > 0, there is δ > 0 such that |x − ε·y| < M for all 0 < ε < δ. The work is repeated per sign, and `h_inactive` uses a separate continuity argument for the strict case.

Proposed change:

Add one scalar helper, for example `exists_delta_abs_sub_mul_lt {x y M : ℝ} (hM : 0 < M) (hx : |x| ≤ M) (hxy : |x| = M → 0 < x * y) : ∃ δ > 0, ∀ ε ∈ Set.Ioo 0 δ, |x − ε * y| < M`. The active case takes δ = |x| / |y|. The inactive case takes δ from continuity, or from an explicit bound. State a second helper rewriting `additiveFunction (fun i => ε * a i) S = ε * additiveFunction a S` (via `Finset.mul_sum`). Then, for the positive and negative active sets, `x = f S` and `y = additiveFunction a S`, and the hypothesis is `0 < f S * additiveFunction a S`. That hypothesis follows from `h_additiveFunction_a_pos` (f S = M) or `h_additiveFunction_a_neg` (f S = −M). `h_inactive`, and the two branches of `h_active`, become a single `obtain ⟨δ, hδ, h⟩ := helper hM_pos (hMbound S) …` per S.

Benefit: This removes about 75 lines of sign-specific `simp_all`/`nlinarith` scripts, which break easily. The new lemma is a natural, reusable statement about moving off a boundary point of the interval [−M, M] in an inward direction. The Hahn–Banach proof then reads as: pick a, then choose ε by the helper.

Source evidence:

- `zero_mem_convexHull_of_best_approx, h_active negative branch` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: ⟨M / (∑ i ∈ S, Λ (Function.update 0 i 1)),
- `zero_mem_convexHull_of_best_approx, h_active positive branch` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: ⟨M / (-∑ i ∈ S, Λ (Function.update 0 i 1)),
- `zero_mem_convexHull_of_best_approx, h_inactive` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: have h_inactive : ∀ S : Finset U, |f S| < M → ∃ ε > 0, ∀ ε' ∈ Set.Ioo 0 ε, |f S -

### repeated-proof-machinery: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L396-L435)

Declaration: `dual_cert_from_convexHull (h_sum_eq: positive and negative generator cases)`

The claim that a generator v is the sum over the two filtered families of `if v = ±S.indicator' then v else 0` is proved twice. The `rcases` branches differ only in the sign. Each branch rewrites with `sum_eq_single S` and `sum_eq_zero`, runs a long `simp +contextual only` list that is the same up to `neg_zero`/`zero_add`/`neg_inj`, and then closes the same side goal: if `T.indicator' = -S.indicator'` or `-T.indicator' = S.indicator'` then T = S. That side goal is proved by two near-identical `congr_fun`/`split_ifs`/`norm_num` blocks. The side goal is simply that `indicator' S` and `-indicator' T` are never equal when `M > 0` and one of them is a nonzero active generator. The same fact is reproved with `grind` and `aesop` in the disjointness step near lines 365–380.

Proposed change:

Prove one lemma next to `indicator'_injective`, for example `indicator'_ne_neg_indicator' {S T : Finset U} (h : S ≠ ∅ ∨ T ≠ ∅) : S.indicator' ≠ -T.indicator'`. Equivalently, `S.indicator' = -T.indicator' → S = ∅ ∧ T = ∅`. Use it in both `sum_eq_single` branches. It also covers the disjointness proof of the images (lines ~365–380), where the case `∅` is handled by hand using `hMbound ∅` and `hM_pos`. Alternatively, define the weight directly as `∑ v ∈ c, if v = S.indicator' …` and avoid the case split by proving `activeGenerators` is the disjoint union of two injective images. Either way, the pos/neg branches shrink to a few lines each.

Benefit: One reusable fact about indicator vectors replaces three ad hoc `congr_fun`/`split_ifs` arguments. The two mirror-image 20-line blocks collapse. The disjointness of positive and negative generators becomes an explicit, nameable property instead of being implicit in `grind`/`aesop` calls.

Source evidence:

- `dual_cert_from_convexHull, positive-generator branch` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: · rw [Finset.sum_eq_single S, Finset.sum_eq_zero] <;>
- `dual_cert_from_convexHull, negative-generator branch` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: split_ifs at this <;> simp_all +decide [Finset.indicator']
- `dual_cert_from_convexHull, disjointness of positive and negative images` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: have h_empty : S₁ = ∅ := by

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L364-L413)

Declaration: `realLerayProjectionRepresentative_isWeakDivFree / realStokesOperatorRepresentative_isWeakDivFree`

Both theorems run the same argument. They apply `realPart_isWeakDivFree_of_fourierOrthogonal`, prove by `change ℱ (ℱ.symm …) = _; exact apply_symm_apply _` that the Fourier transform of the operator output is the multiplier applied to the transformed input, turn that into an a.e. equality with `Lp.ext_iff`, and then `filter_upwards` the transform equality together with the multiplier's a.e. orthogonality fact. Only the operator and the multiplier differ. The `ℱ (ℱ.symm (M (ℱ x))) = M (ℱ x)` step is also repeated in ForcedRegMomentumSlicePressure.lean (`hLZ`).

Proposed change:

Add one helper next to `realPart_isWeakDivFree_of_fourierOrthogonal`:
`theorem realPart_isWeakDivFree_of_fourier_eq_multiplier (w : ComplexVectorL2) (M : ComplexVectorL2) (hw : MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 w = M) (hM : ∀ᵐ ξ ∂volume, inner ℂ (complexifyFrequency ξ) (M ξ) = 0) : CKN.IsWeakDivFreeL2 (realPartVectorL2Representative w)`.
Its proof is the shared `filter_upwards [(Lp.ext_iff).mp hw, hM]` block. Each theorem then reduces to `exact realPart_isWeakDivFree_of_fourier_eq_multiplier _ _ (ℱ.apply_symm_apply _) (lerayFourierMultiplier_divergence_free_ae _)`, and likewise for Stokes with `ℱV`, `stokesFourierMultiplier ht (ℱT _)` and `stokesFourierMultiplier_divergence_free_ae`. This replaces about 17 lines in each theorem with one or two. The `ℱ.apply_symm_apply` step is still needed unless `lerayProjectionL2` and `stokesL2Operator` get their own lemmas for the Fourier transform of their output.

Benefit: The a.e. transfer is written once. Each of the two range theorems becomes a short instantiation, and a future Fourier-multiplier operator with divergence-free range can reuse the helper. The statement is the natural one: a vector field whose Fourier transform equals a frequency-orthogonal field has weakly divergence-free real part.

Source evidence:

- `realStokesOperatorRepresentative_isWeakDivFree` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`:     change ℱV (ℱV.symm
      (stokesFourierMultiplier ht (ℱT (complexifyTensorL2 F)))) = _
    exact ℱV.apply_symm_apply _
- `hLZ in the proof around line 206` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/ForcedRegMomentumSlicePressure.lean`:     unfold lerayProjectionL2
    exact LinearIsometryEquiv.apply_symm_apply _ _

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L384-L424)

Declaration: `realLerayProjection_isWeakDivFree / realStokesOperator_isWeakDivFree`

Both theorems transport weak divergence-freeness from `realPartVectorL2Representative z` to `realVectorL2Representative (realPartVectorL2 z)`. They do this with the same sequence: `realPartVectorL2Representative_eq_ae z`, then `change`, then `isWeakDivFree_congr_ae hAE.symm hRange`. Only `z` differs. The two `…Representative_isWeakDivFree` / `…_isWeakDivFree` pairs therefore each end in a duplicate wrapper.

Proposed change:

Combine the lemmas `isWeakDivFree_congr_ae` and `realPartVectorL2Representative_eq_ae` into one lemma:
`theorem realPartVectorL2_isWeakDivFree_of_representative (z : ComplexVectorL2) (h : CKN.IsWeakDivFreeL2 (realPartVectorL2Representative z)) : CKN.IsWeakDivFreeL2 (realVectorL2Representative (realPartVectorL2 z))`.
Its proof is `isWeakDivFree_congr_ae (realPartVectorL2Representative_eq_ae z).symm h`. The two real-operator theorems then become `realPartVectorL2_isWeakDivFree_of_representative _ (realLerayProjectionRepresentative_isWeakDivFree f)` and the Stokes analogue. Together with the first finding, one lemma could go from `w` with Fourier-orthogonal transform directly to `realVectorL2Representative (realPartVectorL2 w)`. The four end-of-file theorems would then reduce to instantiations.

Benefit: This removes the repeated `let z / have hAE / change / exact` block and states the conversion from the coordinate representative to the `realPartVectorL2` form once. It is a modest gain on its own, but it adds to the first finding.

Source evidence:

- `realStokesOperator_isWeakDivFree` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`:   let z := stokesL2Operator ht (complexifyTensorL2 F)
  have hRange := realStokesOperatorRepresentative_isWeakDivFree ht F
  have hAE := realPartVectorL2Representative_eq_ae z

### readable-proof-simplification: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L64-L73)

Declaration: `Finset.mem_dfinsupp_iff_of_support_subset`

The proof chains `Iff.trans`, `forall_and.symm`, `forall_congr'` and a nested anonymous-constructor term. The nested term contains a `?_` placeholder inside a lambda that is only filled in at the end, in the `rwa [H, mem_zero] at h` bullet. A reader has to decode the combinator chain, and has to work out that `H` and `h` in the last bullet refer to variables bound deep inside the term. The two directions of the biconditional and the order of the goals are not visible.

Proposed change:

Rewrite with `mem_dfinsupp_iff` and state the two directions directly:
```lean
  rw [mem_dfinsupp_iff]
  refine ⟨fun h i => ?_, fun h => ⟨fun i hi => ht (mem_support_iff.2 fun H => ?_), fun i _ => h i⟩⟩
  · by_cases hi : i ∈ s
    · exact h.2 i hi
    · rw [notMem_support_iff.1 (fun hf => hi (h.1 hf)), notMem_support_iff.1 (notMem_mono ht hi)]
      exact zero_mem_zero
  · have := h i
    rw [H, mem_zero] at this
    exact mem_support_iff.1 hi this
```
The `by_cases` branch is the existing argument. The second bullet becomes an explicit step (if `t i = 0` then `f i ∈ 0`, so `f i = 0`) and no longer needs `rwa` on a hidden hypothesis.

Benefit: The `forall_and.symm.trans <| forall_congr'` plumbing and the `?_` placeholders buried in a lambda go away. The proof then reads as the two directions, 'pointwise membership implies the support condition' and 'the converse', with named hypotheses. The mathematical content is unchanged and is easier to follow and maintain.

Source evidence:

- `Finset.mem_dfinsupp_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: theorem mem_dfinsupp_iff : f ∈ s.dfinsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i := by
- `DFinsupp.notMem_support_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Defs.lean`: theorem notMem_support_iff {f : Π₀ i, β i} {i : ι} : i ∉ f.support ↔ f i = 0 :=

### readable-proof-simplification: [Mathlib/Topology/Category/Profinite/EffectiveEpi.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/Category/Profinite/EffectiveEpi.lean#L86-L90)

Declaration: `Profinite.effectiveEpiFamily_tfae`

The step `3 ↔ 1` is proved by using `erw` to rewrite the goal with an `Iff` that carries a type ascription `(… :)`, and then `exact` closes what is left. `erw` is a fragile, defeq-sensitive tactic here. It hides the actual chain of reasoning: the Profinite surjectivity condition is equivalent to the CompHaus effective epi family condition, which is equivalent to the Profinite one. A reader has to run the rewrite mentally to see the remaining goal.

Proposed change:

State the chain directly with `Iff.trans` and no rewriting:

  tfae_have 3 ↔ 1 :=
    ((CompHaus.effectiveEpiFamily_tfae
      (fun a ↦ profiniteToCompHaus.obj (X a)) (fun a ↦ profiniteToCompHaus.map (π a))).out 3 1).trans
      ⟨fun h ↦ profiniteToCompHaus.finite_effectiveEpiFamily_of_map _ _ h,
        fun _ ↦ inferInstance⟩

The first factor is the CompHaus equivalence between joint surjectivity and being an effective epi family. The second factor is the equivalence between the CompHaus family and the Profinite family, with one direction from `finite_effectiveEpiFamily_of_map` and the other from preservation.

Benefit: This removes `erw`, the `( … :)` ascription and the tactic block. The proof becomes a two-step transitivity argument that matches the mathematical idea, and it no longer depends on rewriting up to reducible defeq.

Source evidence:

- `CompHaus.effectiveEpiFamily_of_jointly_surjective` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/Category/CompHaus/EffectiveEpi.lean`: ((effectiveEpiFamily_tfae X π).out 3 1).mp surj
- `List.TFAE.out` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/List/TFAE.lean`: theorem TFAE.out {l} (h : TFAE l) (i j : Nat) {a b}

### readable-proof-simplification: [TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean#L69-L79)

Declaration: `TauCeti.gradedIdempotentHeadBasis_apply and TauCeti.gradedIdempotentHeadBasis_repr_apply`

Each of the two lemmas has a proof that is just `by exact <term>`. The `by exact` wrapper adds a tactic block around what is already a complete term proof. The upstream lemmas `gradedSimpleClassBasis_apply` and `gradedSimpleClassBasis_repr_apply` are themselves stated as term proofs or plain rewrites, so the wrapper adds nothing.

Proposed change:

Write the proofs as terms. For the first lemma, replace `:= by\n  exact gradedSimpleClassBasis_apply _ _ _ _ _ _ i` with `:=\n  gradedSimpleClassBasis_apply _ _ _ _ _ _ i`. For the second lemma, replace `:= by\n  exact gradedSimpleClassBasis_repr_apply _ _ _ _ _ _ x i` with `:=\n  gradedSimpleClassBasis_repr_apply _ _ _ _ _ _ x i`.

Benefit: The proofs read directly as "this is the general lemma specialised to the head family". There is no tactic-mode noise, and the style matches the term-mode proof of the upstream lemma `gradedSimpleClassBasis_apply`.

Source evidence:

- `TauCeti.gradedSimpleClassBasis_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/SimpleBasis.lean`:   Module.Basis.mk_apply _ _ i
- `TauCeti.gradedSimpleClassBasis_repr_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/SimpleBasis.lean`: gradedIdempotentCoordinate (he i) (he₀ i) x := by

### readable-proof-simplification: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L280-L294)

Declaration: `TauCeti.ReducedTensorWords.eq_of_letter_comp_eq_of_twist`

`hletter`, `happly₁` and `happly₂` each spend a `by` block on the same boilerplate: `congrArg (fun f ↦ f z)` to apply the equation, then a `simpa only [coe_comp, comp_apply, add_apply]` to unfold the composite. That is 15 lines, and the three blocks differ only in the hypothesis. The dedicated lemma `LinearMap.congr_fun` is already used for this in neighbouring files (for example `Primitives.lean` and `OddSquare.lean`). The unfolding of `comp_apply` and `add_apply` is definitional, so the stated pointwise forms should be accepted directly.

Proposed change:

Keep the stated types of `hletter`, `happly₁` and `happly₂`, which are what the later `rw [happly₁, happly₂]` needs. Replace each proof by the lemma applied to the hypothesis:
`have hletter : ∀ z, letter R M (b₁ z) = letter R M (b₂ z) := LinearMap.congr_fun hl`
`have happly₁ : ∀ z, deconcatenation R M (b₁ z) = ... := LinearMap.congr_fun h₁`
`have happly₂ : ∀ z, deconcatenation R M (b₂ z) = ... := LinearMap.congr_fun h₂`
If elaboration needs help, use `fun z ↦ by simpa only [LinearMap.comp_apply, LinearMap.add_apply] using LinearMap.congr_fun h₁ z`. That still removes the `congrArg` lambda and the `have h` step.

Benefit: This removes about ten lines of repeated unfolding. A reader sees that each fact is just the hypothesis applied pointwise, so the filtration induction is easier to follow. It also matches how the rest of the library applies equalities of linear maps to elements.

Source evidence:

- `LinearMap.congr_fun` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Algebra/Module/LinearMap/Defs.lean`: protected theorem congr_fun (h : f = g) (x : M) : f x = g x :=
- `hFb (local have)` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/GradedCoalgHom.lean`: have hFb : ∀ z, bN (F z) = F (bM z) := LinearMap.congr_fun hF

### readable-proof-simplification: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L231-L232)

Declaration: `TauCeti.ReducedTensorWords.IsCoderivation.deconcatenation_apply`

The proof applies the equation to `z` with a hand-written `congrArg (fun f ↦ f z)` and then unfolds with a `simpa`. `LinearMap.congr_fun` states exactly this application, and the unfolding is definitional.

Proposed change:

Use `LinearMap.congr_fun hb z` as the whole proof. If the defeq unfolding of `comp_apply` and `add_apply` is not accepted, use `by simpa only [LinearMap.comp_apply, LinearMap.add_apply] using LinearMap.congr_fun hb z`. Since `IsCoderivation` is a `def`, the unfolding may need `isCoderivation_iff.1 hb`.

Benefit: The proof becomes a one-line term that says plainly that the pointwise rule is the co-Leibniz equation applied at `z`. It also agrees with the `LinearMap.congr_fun` idiom used elsewhere in the library.

Source evidence:

- `LinearMap.congr_fun` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Algebra/Module/LinearMap/Defs.lean`: protected theorem congr_fun (h : f = g) (x : M) : f x = g x :=
- `(use of LinearMap.congr_fun)` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/Primitives.lean`: exact LinearMap.congr_fun h w

### readable-proof-simplification: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L130-L137)

Declaration: `zero_mem_convexHull_of_best_approx (Hahn–Banach separation step)`

The separation hypotheses are bundled into a conjunction `h_closed_convex` and then projected back out. The lemma is stated through `@` and applied with `convert`, which is unnecessary because the result type already matches the `obtain` statement (`StrongDual ℝ E` is `E →L[ℝ] ℝ`). The whole block only needs convexity, closedness and `x ∉ s`.

Proposed change:

Apply the lemma directly:
```lean
obtain ⟨Λ, u, hΛ, hu⟩ := geometric_hahn_banach_closed_point
  (convex_convexHull ℝ _)
  (Set.Finite.isClosed_convexHull ℝ (activeGenerators_finite f M)) h_contra
```
The explicit type ascription on the `obtain` can then be dropped, or kept as `: ∃ Λ : (U → ℝ) →L[ℝ] ℝ, ...` if preferred.

Benefit: This replaces about 8 lines of conjunction building, `@`, and `convert` with one self-explanatory call. A reader sees exactly the three hypotheses of the Hahn–Banach separation theorem: convex, closed, and the point is not in the set. It also removes the risk of `convert` producing side goals.

Source evidence:

- `geometric_hahn_banach_closed_point` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/LocallyConvex/Separation.lean`: theorem geometric_hahn_banach_closed_point (hs₁ : Convex ℝ s) (hs₂ : IsClosed s) (disj : x ∉ s) :
- `Set.Finite.isClosed_convexHull` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Convex/Topology.lean`: theorem Set.Finite.isClosed_convexHull [T2Space E] {s : Set E} (hs : s.Finite) :

### readable-proof-simplification: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L252-L262)

Declaration: `zero_mem_convexHull_of_best_approx (choice of a uniform ε)`

The minimum of the finitely many ε S is built by hand. The code splits on whether `Finset.univ : Finset (Finset U)` is nonempty, which is always true because `∅` is a finset. It then builds an image finset with `min'`, and the empty branch is discharged by `simp_all`. This is an unnecessary case split and a manual `min'` construction.

Proposed change:

Use `Finite.exists_min` on the finite, nonempty type `Finset U`:
```lean
obtain ⟨S₀, hS₀⟩ := Finite.exists_min ε
exact ⟨ε S₀ / 2, half_pos (hε_pos S₀), fun S =>
  hε S (ε S₀ / 2) ⟨half_pos (hε_pos S₀), by linarith [hS₀ S, hε_pos S₀]⟩⟩
```
This also removes the intermediate `ε_min` statement.

Benefit: The argument becomes: take the index where the positive function ε is smallest, then use half of its value. This is the intended mathematics. It removes the vacuous empty-case branch and the `simp_all +decide` calls, and it is easier to follow.

Source evidence:

- `Finite.exists_min` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Data/Fintype/Lattice.lean`: theorem Finite.exists_min [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :

### readable-proof-simplification: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L285-L312)

Declaration: `dual_cert_from_convexHull (extraction of positive weights, first `obtain`)`

The code starts from the indexed-family characterisation of the convex hull. It then re-indexes by images of `z` over the filter `w i ≠ 0`, proves positivity and sums via `sum_image'`, `sum_filter_of_ne` and `simp_all`, all to obtain a finset of vectors with weights. Mathlib already states the convex hull of a finite set directly as weights on the finset. The generator set is known to be finite (`activeGenerators_finite`), so the re-indexing is avoidable.

Proposed change:

Use the finite-set characterisation instead:
```lean
have hfin := activeGenerators_finite f M
rw [hfin.convexHull_eq] at h0
obtain ⟨w, hw_nonneg, hw_sum, hw_cm⟩ := h0
-- c := hfin.toFinset, membership from `hfin.mem_toFinset`,
-- and `Finset.centerMass_eq_of_sum_1` turns centerMass into ∑ w v • v
```
Alternatively, rewrite `hfin.coe_toFinset` and use `Finset.mem_convexHull'`, which gives `∑ y ∈ s, w y • y = x` directly. The weights are only nonnegative rather than strictly positive. The downstream use of positivity (`le_of_lt` for `lam_pos` nonnegativity, and membership via `hw_pos`) must be adapted to use `hw_nonneg`. Strict positivity is not needed for the support conditions, which come from membership in `c`.

Benefit: This removes about 28 lines of image/filter bookkeeping. The statement that `0` is a convex combination of finitely many generators is then read directly from the Mathlib lemma. Fewer `simp_all` calls and explicit `sum_image'` arguments means less fragile proof text.

Source evidence:

- `Finset.mem_convexHull'` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Convex/Combination.lean`: ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ ∑ y ∈ s, w y = 1 ∧ ∑ y ∈ s, w y • y = x
- `Set.Finite.convexHull_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Convex/Combination.lean`: theorem Set.Finite.convexHull_eq {s : Set E} (hs : s.Finite) : convexHull R s =

### readable-proof-simplification: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L179-L185)

Declaration: `zero_mem_convexHull_of_best_approx (h_inactive)`

The existential obtained from the limit statement is kept as an anonymous `this`. It is then taken apart three times with `this.choose` and `this.choose_spec`, which makes the final term hard to read and gives it non-obvious dependencies on choice.

Proposed change:

Destructure once:
```lean
obtain ⟨δ, hδ, h⟩ := Metric.tendsto_nhdsWithin_nhds.mp h_cont (M - |f S|) (sub_pos.mpr hS)
refine ⟨δ, hδ, fun ε' hε' => ?_⟩
linarith [abs_lt.mp (h hε'.1 (by simpa [abs_of_pos hε'.1] using hε'.2))]
```
This keeps the same inner argument, which is unchanged from the original.

Benefit: Named `δ`, `hδ` and `h` make the ε–δ argument readable. They also remove the repeated `.choose` / `.choose_spec` projections and the large anonymous-constructor term.

Source evidence:

- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: ⟨this.choose, this.choose_spec.1, fun ε' hε' => by

### readable-proof-simplification: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L151-L169)

Declaration: `CKN.Leray.weakTestGradientSchwartz_apply`

The proof rebuilds the chain rule for composition with the continuous linear equivalence `l2Vec3Equiv` by hand. It proves `hψSource` (smoothness) and `hL` (the derivative of the equivalence). It then uses `fderiv_comp` with two differentiability side conditions, and finishes with a `calc` that rewrites with `hL`. That is about 18 lines for a standard fact. Mathlib states it directly as `ContinuousLinearEquiv.comp_right_fderiv`, with no differentiability hypotheses. `hψSource` is used only inside `hcomp'`, so it disappears too.

Proposed change:

Replace `hψSource`, `hL` and the `calc` in `hcomp'` with a single step:
```lean
  have hcomp' :
    fderiv ℝ (fun z : L2Vec3 => weakTestSourceSchwartz ψ (l2Vec3Equiv z)) x =
        (fderiv ℝ (weakTestSourceSchwartz ψ) (l2Vec3Equiv x)).comp
          (l2Vec3Equiv : L2Vec3 →L[ℝ] Vec3) :=
    l2Vec3Equiv.comp_right_fderiv
```
The statement of `hcomp'` stays the same, and the rest of the proof is unchanged. If elaboration of the lambda against `f ∘ iso` needs help, use `by simpa [Function.comp_def] using l2Vec3Equiv.comp_right_fderiv (f := weakTestSourceSchwartz ψ) (x := x)`.

Benefit: The key idea is that the derivative of `f ∘ equiv` is `(fderiv f (equiv x)).comp equiv`. It is now stated once and justified by a named Mathlib lemma. The reader no longer has to follow smoothness and differentiability side goals that have nothing to do with the main argument. The proof is about 18 lines shorter.

Source evidence:

- `ContinuousLinearEquiv.comp_right_fderiv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/FDeriv/Equiv.lean`: fderiv 𝕜 (f ∘ iso) x = (fderiv 𝕜 f (iso x)).comp (iso : E →L[𝕜] F)
- `CKN.Leray.weakTestGradientSchwartz_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: _ = _ := by rw [hL]
