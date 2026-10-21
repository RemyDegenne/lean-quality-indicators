# Findings


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

### statement-generality: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L106-L113)

Declaration: `Algebra.TensorProduct.instFree`

`instFree` assumes `[CommSemiring A]`, but nothing in its proof needs commutativity of `A`. It is proved from `Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)`. That `basis` is defined in the same file under `[Semiring A] [Algebra R A]`. `Module.Free A _` and `Module.Free.of_basis` only need a `Semiring A`. The instance therefore does not apply to a noncommutative `R`-algebra `A`, such as a matrix algebra over `R`, even though the basis construction above it does.

Proposed change:

Replace `[CommSemiring A] [Algebra R A]` with `[Semiring A] [Algebra R A]` in `instFree`. Keep the proof `Module.Free.of_basis <| Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)`. The `Module A (A ⊗[R] M)` instance already elaborates in the `Semiring A` section for `basis`, so the statement should elaborate unchanged. The `CommSemiring A` instances remain applicable for commutative `A`, since they supply a `Semiring A`.

Benefit: Freeness of the base change becomes available as an instance for noncommutative algebras `A`. This matches the generality of `Algebra.TensorProduct.basis` and the module structure. Existing commutative uses are unaffected, because the commutative instances still supply a `Semiring A`.

Source evidence:

- `Algebra.TensorProduct.basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: variable [CommSemiring R] [Semiring A] [Algebra R A]
- `LinearMap.baseChange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/TensorProduct/Tower.lean`: def baseChange (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=

### statement-generality: [Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean#L60-L64)

Declaration: `instance (F : ℕ ⥤ C) : F.IsWellOrderContinuous (and the Fin n instance)`

The ℕ instance and the `Fin n` instance both hold for the same reason. Neither type has a successor limit, and the Fin proof already uses only `Order.not_isSuccLimit_of_isSuccArchimedean`. That lemma holds for any `Preorder` with a `SuccOrder` and `IsSuccArchimedean`. The same argument covers ℤ, and any other order with these classes, so the two instances are special cases of one statement. The ℕ proof (`simp at hm`) also depends on the simp lemma for the same fact.

Proposed change:

Replace the two concrete instances with one general instance:

instance (priority := low) [SuccOrder J] [IsSuccArchimedean J] (F : J ⥤ C) : F.IsWellOrderContinuous where
  nonempty_isColimit _ hm := (Order.not_isSuccLimit_of_isSuccArchimedean hm).elim

The proof is the one the Fin instance already uses. The ℕ and Fin n instances then follow from the existing `IsSuccArchimedean` instances. The only degenerate case is an empty or minimal element. `IsSuccLimit` excludes minimal elements, and `not_isSuccLimit_of_isSuccArchimedean` gives `¬ IsSuccLimit a` for every `a` unconditionally. If instance search is a concern, keep a single lemma with this statement and state the ℕ and Fin n instances through it.

Benefit: Users get the instance for ℤ and for any other successor-Archimedean index category, such as a finite chain given as a subtype, without writing a new instance. The file also loses two near-duplicate proofs and one `simp`-based proof that depends on simp-set behaviour.

Source evidence:

- `Order.not_isSuccLimit_of_isSuccArchimedean` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Limit.lean`: theorem not_isSuccLimit_of_isSuccArchimedean : ¬ IsSuccLimit a :=
- `instance : IsSuccArchimedean ℤ` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Int.lean`: instance : IsSuccArchimedean ℤ :=
- `IsSuccArchimedean` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Archimedean.lean`: class IsSuccArchimedean (α : Type*) [Preorder α] [SuccOrder α] : Prop where

### statement-generality: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L399-L494)

Declaration: `Bundle.Trivialization.continuousLinearMapAt / symmL / continuousLinearEquivAt / apply_eq_prod_continuousLinearEquivAt / Trivialization.zeroSection`

These declarations are stated under the section-wide hypotheses `[NontriviallyNormedField R] [NormedAddCommGroup F] [NormedSpace R F]`. Their proofs use none of the norm structure. `continuousLinearMapAt` uses `continuous_if_const`, `continuous_zero`, `Trivialization.continuousOn` and `FiberBundle.totalSpaceMk_isInducing`. `symmL` uses `continuousOn_symm` and `totalSpaceMk_isInducing`. `continuousLinearEquivAt` uses the same facts plus `symmL`. `Trivialization.zeroSection` only uses `map_zero` of the equiv. `FiberBundle` itself only needs `[TopologicalSpace B] [TopologicalSpace F]`, and `E b →L[R] F` only needs `[Semiring R]` with topological module structures. The earlier section of this file already treats `coordChangeL : F ≃L[R] F` under `[Semiring R] [TopologicalSpace F] [TopologicalSpace B]`, so the file is inconsistent about this. The `IsLinear` mixin is likewise stated for a `Semiring`.

Proposed change:

Move this block (`continuousLinearMapAt`, `continuousLinearMapAt_apply_of_mem`, `symmL`, `symmL_apply`, `symmL_apply_of_notMem`, `symmL_continuousLinearMapAt`, `continuousLinearMapAt_symmL`, `continuousLinearEquivAt` and its `_eq` / `_apply'` lemmas, `apply_eq_prod_continuousLinearEquivAt`, `Trivialization.zeroSection`) into a section with `[Semiring R] [TopologicalSpace B] [TopologicalSpace F] [AddCommMonoid F] [Module R F] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)] [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]`. Keep the proofs unchanged. Leave `continuous_zeroSection` and the other `VectorBundle`-dependent results under the normed hypotheses.

Benefit: The trivialization API becomes available for topological vector bundles over arbitrary topological semirings or rings and non-normed fibers, for example locally convex, non-normable or merely topological modules. Today the `IsLinear`/`coordChangeL` API in the first section works there, but these continuous-linear-equivalence lemmas do not. The hypotheses then match what the proofs use, and users no longer have to pull in a `NontriviallyNormedField` just to use `continuousLinearEquivAt`.

Source evidence:

- `FiberBundle` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/FiberBundle/Basic.lean`: variable [TopologicalSpace B] [TopologicalSpace F] (E : B → Type*)
- `Bundle.Trivialization.coordChangeL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: def coordChangeL (e e' : Trivialization F (π F E)) [e.IsLinear R] [e'.IsLinear R] (b : B) :
    F ≃L[R] F :=
- `section variable block` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: variable [NontriviallyNormedField R] [∀ x, AddCommMonoid (E x)] [∀ x, Module R (E x)]

### statement-generality: [Mathlib/Control/Traversable/Equiv.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Control/Traversable/Equiv.lean#L38-L83)

Declaration: `Equiv.map / Equiv.functor / Equiv.id_map / Equiv.comp_map / Equiv.lawfulFunctor / Equiv.lawfulFunctor' (Functor section)`

The Functor section is stated only for `t t' : Type u → Type u`. Nothing in it uses that restriction. `Functor` and `LawfulFunctor` are universe-polymorphic, taking `Type u → Type v`. The definitions and proofs use only `Functor.map`, `id_map`, `map_const` and the equivalences `eqv α`, so they never need the codomain universe to equal the domain universe. The restriction comes from the later Traversable section, whose class (`Traversable (t : Type u → Type u)`) needs it. As a result, transferring a `Functor` or `LawfulFunctor` along an isomorphism is unavailable for functors such as `Type u → Type (max u v)`.

Proposed change:

Add a universe `v` and change the first Functor-section variable line to `variable {t t' : Type u → Type v} (eqv : ∀ α, t α ≃ t' α)`. Also change `{α β γ : Type u}` in `Equiv.map`, `id_map` and `comp_map` as needed. The statements and proof scripts stay the same. The Traversable section keeps `Type u → Type u` and still uses these declarations, because it is the `v := u` instance. The `simp [Equiv.map, id_map]` proofs and the structure literal for `lawfulFunctor` should carry over, but I have not compiled them.

Benefit: The transfer of `Functor` and `LawfulFunctor` instances along natural isomorphisms would apply to every functor `Type u → Type v`, matching the generality of the `Functor` and `LawfulFunctor` classes. The Traversable section's use would be unchanged. This is a low-cost generalisation that does not obscure the statements.

Source evidence:

- `Traversable` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Control/Traversable/Basic.lean`: class Traversable (t : Type u → Type u) extends Functor t where

### statement-generality: [TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L116-L127)

Declaration: `Matrix.SpecialOrthogonalGroup.eq_one_of_mem_center_of_odd`

The hypothesis `3 ≤ Fintype.card n` is only a side condition for `mem_center_iff`. Odd dimension already gives `1 ≤ Fintype.card n`. The only case the bound excludes is dimension 1, where `specialOrthogonalGroup n R` is trivial because `det g = g default default = 1`. So the odd-dimension triviality is true without `hn`, but the statement is restricted to n ≥ 3 and the docstring repeats the restriction. The intended mathematics is not changed; the statement is just narrower than the truth.

Proposed change:

State the lemma as `theorem eq_one_of_mem_center_of_odd (h2 : IsRegular (2 : R)) (g : specialOrthogonalGroup n R) (hodd : Odd (Fintype.card n)) (hg : g ∈ Subgroup.center (specialOrthogonalGroup n R)) : g = 1`. For the proof, do `by_cases hn : 3 ≤ Fintype.card n`. If it holds, run the current argument unchanged. Otherwise `Odd (card n)` forces `Fintype.card n = 1`, since card 0 is even and card 2 is even. Then `Fintype.card_eq_one_iff` gives a `Unique n`. `Matrix.det_unique` together with `(mem_specialOrthogonalGroup_iff.mp g.2).2` shows the single entry is 1, and `Subtype.ext` plus `ext i j` (with i = j = default) closes the goal. Equivalently, the 1×1 case could be a separate lemma.

Benefit: Callers no longer have to prove an artificial `3 ≤ n` for odd n. The downstream `eq_one_of_isCentralPoint_of_odd` needs `hn` only for `isCentralPoint_iff_mem_center_pointsMulEquiv`, so it also becomes easier to generalise. The result becomes the clean statement that every odd-dimensional special orthogonal group has trivial center, with n = 1 covered.

Source evidence:

- `TauCeti.SpecialOrthogonal.eq_one_of_isCentralPoint_of_odd` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/AlgebraicGroup/SpecialOrthogonal/Center.lean`: (pointsMulEquiv R n (A := A) g) (by simpa using hn) (by simpa using hodd)
- `Matrix.SpecialOrthogonalGroup.mem_center_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean`: have hdet := (mem_specialOrthogonalGroup_iff.mp g.2).2

### statement-generality: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L67-L73)

Declaration: `TauCeti.sum_filter_eq_zero_of_mem_Ioo`

The lemma only uses that no prevertex with nonzero exponent sits exactly at `x`. The interval `Ioo p q` and the membership `hx` are an unnecessary detour: the proof just specialises the interval hypothesis at `x`. This is a weakening of the hypothesis, from an interval-wide condition to a pointwise one. It also makes the lemma unusable for points that are not prevertices but have no free interval around them, for example a general set `s` in `continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one`. The lemma is also stated only for `ℝ`-valued `a` and `e`, although the proof uses nothing about `ℝ`.

Proposed change:

State the core lemma pointwise and generically, with `{α M : Type*} [DecidableEq α] [AddCommMonoid M] (a : ι → α) (e : ι → M) {x : α} (ha : ∀ i, e i ≠ 0 → a i ≠ x) : ∑ i with a i = x, e i = 0`. Proof: `Finset.sum_eq_zero fun i hi => by_contra fun he => ha i he (Finset.mem_filter.mp hi).2`. Then keep `sum_filter_eq_zero_of_mem_Ioo` as a one-line corollary, applying the generic lemma with `fun i he h => ha i he (h ▸ hx)`. If the corollary is only used in `continuousOn_schwarzChristoffelBoundary_Icc`, it could be inlined.

Benefit: Users get a reusable fact: at any point that is not a nonzero-exponent prevertex, the total exponent is 0, hence greater than -1. This applies directly to `tendsto_schwarzChristoffelPrimitive_boundary` and to sets of non-prevertex points, and does not require choosing an auxiliary interval. The generic form also works for other index, exponent or parameter types.

Source evidence:

- `TauCeti.sum_filter_eq_zero_of_mem_Ioo` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`: exact ha i he (by simpa only [(Finset.mem_filter.mp hi).2] using hx)
- `TauCeti.continuousOn_schwarzChristoffelBoundary_Icc` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`: rw [sum_filter_eq_zero_of_mem_Ioo a e ha ⟨hpx, hxq⟩]

### statement-generality: [TauCeti/Analysis/Fredholm/ContinuousFamily.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Fredholm/ContinuousFamily.lean#L88-L103)

Declaration: `TauCeti.index_eq_of_segment (section Segment)`

The segment theorem is stated only for fields satisfying `IsRCLikeNormedField`, with a separate set of variables K', E', F' that duplicates the general ones. It also assumes a full `NormedSpace ℝ (E' →L[K'] F')`. The proof's only use of the RCLike structure is `let := IsRCLikeNormedField.rclike K'`, and nothing after it needs that instance. The remaining steps need only `Path.segment` and `AffineMap.lineMap_apply_module`, which require a real module structure on the operator space with continuous addition and continuous real scalar multiplication. `Path.index_eq` is already proved for an arbitrary `NontriviallyNormedField K`. So the statement is more specialised than its proof: it excludes other nontrivially normed fields that carry a compatible real module structure on the operator space. The assumed `NormedSpace ℝ` also adds a norm that the argument does not use.

Proposed change:

Drop the `Segment` section's duplicate variables and the `IsRCLikeNormedField` hypothesis, and use the file's ambient `K E F`. Replace `[NormedSpace ℝ (E' →L[K'] F')]` by the weaker `[Module ℝ (E →L[K] F)] [ContinuousSMul ℝ (E →L[K] F)]`. The statement becomes `theorem index_eq_of_segment [Module ℝ (E →L[K] F)] [ContinuousSMul ℝ (E →L[K] F)] (T S : E →L[K] F) : (∀ t : unitInterval, ContinuousLinearMap.IsFredholm ((1 - (t : ℝ)) • T + (t : ℝ) • S)) → ContinuousLinearMap.index T = ContinuousLinearMap.index S`. The proof is the same without the `let`: `intro h; apply Path.index_eq (Path.segment T S); simpa only [Path.segment_apply, AffineMap.lineMap_apply_module] using h`. `ContinuousAdd` comes from the normed additive group on `E →L[K] F`, and `Path.segment` needs no more than `Module ℝ`, `ContinuousAdd` and `ContinuousSMul ℝ`. When `K` is ℝ or ℂ, the existing normed-space instance supplies both new assumptions, so current uses still elaborate.

Benefit: Users get the segment criterion for any complete nontrivially normed field with a compatible real structure, with no RCLike hypothesis and no norm on the real module structure. The `Segment` section and its duplicated variable block disappear. The statement then matches what the proof actually uses.

Source evidence:

- `Path.segment` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Analysis/Convex/PathConnected.lean`: variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
- `AffineMap.lineMap_apply_module` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/LinearAlgebra/AffineSpace/AffineMap.lean`: theorem lineMap_apply_module (p₀ p₁ : V1) (c : k) : lineMap p₀ p₁ c = (1 - c) • p₀ + c • p₁
- `Path.index_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Fredholm/ContinuousFamily.lean`: theorem _root_.Path.index_eq {T S : E →L[K] F} (A : Path T S)

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

### statement-generality: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L316-L326)

Declaration: `NumberField.Odlyzko.abs_poitouKernel_regularizedScaledTartar_le_gaussian`

The proof uses only the fact that poitouKernel f x = f x / cosh (x/2) with cosh ≥ 1. It never uses any property of regularizedScaledTartar apart from the Gaussian bound on |f x|. The real content, |poitouKernel f x| ≤ |f x| for every f : ℝ → ℝ, is buried inside the Tartar-specific statement and re-derived with an awkward simpa/mul_le_mul_of_nonneg_left step.

Proposed change:

Add a general lemma `theorem abs_poitouKernel_le (f : ℝ → ℝ) (x : ℝ) : |poitouKernel f x| ≤ |f x|`. Proof: `rw [poitouKernel, abs_div, abs_of_pos (Real.cosh_pos _)]; exact div_le_self (abs_nonneg _) (Real.one_le_cosh _)`. Then restate the current lemma as `(abs_poitouKernel_le _ x).trans (abs_regularizedScaledTartar_le_gaussian y δ x)`. The same general lemma works for any other test function f with a pointwise bound, and the file's own derivative bounds (`abs_poitouKernelDerivative_le`, `abs_poitouKernelSecondDerivative_le`) are already stated for arbitrary f.

Benefit: The general inequality becomes reusable for other test functions, and the Tartar-specific lemma becomes a one-line corollary. Readers can see that the cosh factor only ever helps, and the awkward calc disappears. The degenerate case f x = 0 is covered, since div_le_self only needs 0 ≤ |f x| and 1 ≤ cosh.

Source evidence:

- `NumberField.Odlyzko.poitouKernel` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/PoitouTransform.lean`: noncomputable def poitouKernel (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x / Real.cosh (x / 2)
- `NumberField.Odlyzko.abs_regularizedScaledTartar_le_gaussian` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: |regularizedScaledTartar y δ x| ≤ Real.exp (-δ * x ^ 2)

### statement-generality: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L168-L170)

Declaration: `ennreal_mul_rpow`

The statement assumes x ≠ 0, x ≠ ∞ and two unnamed hypotheses on y, then proves (x*y)^e = x^e*y^e by a ~25-line case split on the sign of e with inverses. The identity already holds under much weaker conditions. Mathlib has ENNReal.mul_rpow_of_ne_zero (x ≠ 0, y ≠ 0, any real exponent) and ENNReal.mul_rpow_of_ne_top (both ≠ ⊤, any real exponent). The helper is therefore a strictly more specialised, hand-proved version of a library lemma.

Proposed change:

Delete ennreal_mul_rpow. At the two call sites in positive_shell_scale_identity, use `ENNReal.mul_rpow_of_ne_zero hSn0 hT0 (-(5 - β))` and `ENNReal.mul_rpow_of_ne_zero hSn2_0 hT0 α`. The hxtop/hTTop arguments are then unnecessary at those calls. Because the first two hypotheses are now only ≠ 0, hSnTop and hSn2_Top also become unused.

Benefit: This removes a long private proof and makes the rpow-multiplication step rest on the general library lemma. The lemma needs only nonvanishing and no finiteness side conditions, so the call sites lose several auxiliary facts.

Source evidence:

- `ENNReal.mul_rpow_of_ne_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`: theorem mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z
- `ENNReal.mul_rpow_of_ne_top` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`: theorem mul_rpow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z

### statement-generality: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L27-L28)

Declaration: `cylinderAbsIntegral_le_morreyNorm`

The only use of hq in the proof is `hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq`, and then `hq0.ne'` in the `simpa` that unfolds morreyCell. Nothing uses q ≥ 1. The morreyCell definition is `(ENNReal.ofReal r) ^ (-(Q * (1 - p / q) / p)) * ...` with p = 1. The cancellation of r^(5(1-1/q)) against r^(-(5(1-1/q))) holds for any q ≠ 0, so the lemma is true for every q > 0.

Proposed change:

State it with `(hq : 0 < q)` and use it directly in place of hq0, deleting the `have hq0` line. Callers that have `1 ≤ q` can pass `lt_of_lt_of_le zero_lt_one hq`. The same weakening can be applied to the downstream positive_shell_integral_le if its other hypotheses allow.

Benefit: The cylinder-integral bound becomes usable for Morrey exponents q in (0,1). Its statement also shows that no integrability exponent condition is needed here.

Source evidence:

- `cylinderAbsIntegral_le_morreyNorm` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: simpa [morreyCell, one_div, hq0.ne'] using hcell
- `morreyCell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Basic.lean`: (ENNReal.ofReal r) ^ (-(Q * (1 - p / q) / p)) *

### statement-generality: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L42-L43)

Declaration: `RS.taylorCoeffAt (and the whole ℂ-specialised development, e.g. AnalyticAt.iterate_dslope, HasFPowerSeriesAt.taylorCoeffAt_eq, taylorCoeffAt_add, taylorCoeffAt_sub_pow_mul, AnalyticAt.exists_taylor_remainder)`

The definition and every theorem is fixed to ℂ → ℂ, yet nothing is complex-specific: `dslope`, `slope`, `deriv`, `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`, `FormalMultilinearSeries.coeff_iterate_fslope`, `pow_sub_smul_iterate_dslope_of_zero` are all stated for `[NontriviallyNormedField 𝕜]` (and the dslope/power-series ones for `E` a normed space over 𝕜). The only proof-level uses of ℂ are the `AnalyticAt ℂ`/`HasFPowerSeriesAt` binders and `FormalMultilinearSeries ℂ ℂ ℂ`. This forces users over ℝ (or ℂ-valued maps from ℝ-style 𝕜, p-adic fields, vector-valued functions) to re-develop the same API.

Proposed change:

Replace `ℂ` by a variable `{𝕜 : Type*} [NontriviallyNormedField 𝕜]` (and, for the definition and the lemmas that only use dslope/power-series bridge, optionally a codomain `{E} [NormedAddCommGroup E] [NormedSpace 𝕜 E]`): `noncomputable def taylorCoeffAt (g : 𝕜 → E) (z₀ : 𝕜) (j : ℕ) : E := (Function.swap dslope z₀)^[j] g z₀`. Then `AnalyticAt.iterate_dslope`, `HasFPowerSeriesAt.taylorCoeffAt_eq` (with `p : FormalMultilinearSeries 𝕜 𝕜 E`), `taylorCoeffAt_congr`, `taylorCoeffAt_add`, `_fun_sum` go through unchanged (same Mathlib lemmas, which are already stated over 𝕜, E). The multiplicative lemmas (`_const_mul`, `_sub_pow_mul`, `_monomial`, `exists_taylor_remainder`) can be stated for `g : 𝕜 → 𝕜` over any nontrivially normed field (or with `•` for E-valued g, using `dslope_sub_smul_of_ne` as the proof of `dslope_sub_mul` already does). Specialising to ℂ is then just `𝕜 := ℂ`.

Benefit: The same Taylor-coefficient API becomes usable for real-analytic, vector-valued and non-archimedean settings, and the file's statements match the generality of the Mathlib lemmas they wrap, with no additional mathematics.

Source evidence:

- `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Analytic/IsolatedZeros.lean`: theorem has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀
- `variable block (general 𝕜, E)` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Analytic/IsolatedZeros.lean`: variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E]
- `dslope` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/DSlope.lean`: variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

### statement-generality: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L65-L71)

Declaration: `Filter.EventuallyEq.dslope_eq`

This is a general fact about `dslope`, but is stated only for `f g : ℂ → ℂ`. The proof only uses `dslope_same`, `dslope_of_ne`, `EventuallyEq.deriv_eq`, and unfolding `slope`; the `slope_def_field` rewrites (which force a field codomain) are the only place the codomain is used, and they can be replaced by unfolding `slope` (`slope f a b = (b - a)⁻¹ • (f b - f a)`), which rewrites with `hb`, `hz` equally well.

Proposed change:

State it with `{𝕜 E} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : 𝕜 → E} {z₀ : 𝕜}`: `theorem Filter.EventuallyEq.dslope_eq (hfg : f =ᶠ[𝓝 z₀] g) : dslope f z₀ =ᶠ[𝓝 z₀] dslope g z₀`. Proof sketch: same case split; in the `b ≠ z₀` case use `rw [dslope_of_ne _ hbz, dslope_of_ne _ hbz, slope, slope]` (or `simp only [slope_def_module]`) followed by `rw [hb, hz]`; the `b = z₀` case is unchanged (`dslope_same`, `hfg.deriv_eq`, which is already general).

Benefit: A reusable, Mathlib-style lemma about `dslope` (a candidate for Mathlib's DSlope file) that is applicable to real/vector-valued functions and not tied to this ℂ-valued file; also makes the ℂ version a special case.

Source evidence:

- `dslope_of_ne` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/DSlope.lean`: theorem dslope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a b = slope f a b
- `dslope_same` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/DSlope.lean`: theorem dslope_same (f : 𝕜 → E) (a : 𝕜) : dslope f a a = deriv f a

### statement-generality: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L82-L96)

Declaration: `RS.dslope_const_mul, RS.dslope_const (and similarly RS.dslope_sub_mul)`

These are generic identities about `dslope` but are stated only over ℂ. The proofs use `deriv_const_mul_field`, `slope_def_field`, `ring` and `simp`, which are all valid over any nontrivially normed field; `dslope_const` is even valid for constants valued in any normed space E (`dslope (fun _ : 𝕜 => c) a = fun _ => 0`, using `slope_fun_def`/`simp`). Likewise `dslope_sub_mul` (line 156) uses `hasDerivAt_id`, `HasDerivAt.mul` and `dslope_sub_smul_of_ne`, all general.

Proposed change:

Declare `{𝕜 : Type*} [NontriviallyNormedField 𝕜]` and state `dslope_const_mul (c : 𝕜) (g : 𝕜 → 𝕜) (z₀ : 𝕜)`, `dslope_const {E} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (c : E) (z₀ : 𝕜) : dslope (fun _ : 𝕜 => c) z₀ = fun _ => 0`, and `dslope_sub_mul {F : 𝕜 → 𝕜} (hF : DifferentiableAt 𝕜 F z₀) : dslope (fun z => (z - z₀) * F z) z₀ = F`. The existing proofs should carry over verbatim since `deriv_const_mul_field`, `slope_def_field`, `HasDerivAt.mul` are stated for a general `𝕜`/`𝕜'`.

Benefit: Gives reusable `dslope` lemmas not tied to ℂ, usable together with the generalised `taylorCoeffAt` API (e.g. for real-variable use) and as candidates for Mathlib's DSlope file; the ℂ versions follow by instantiation.

Source evidence:

- `deriv_const_mul_field` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/Deriv/Mul.lean`: theorem deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v x
- `slope_def_field` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/LinearAlgebra/AffineSpace/Slope.lean`: theorem slope_def_field (f : k → k) (a b : k) : slope f a b = (f b - f a) / (b - a)
- `dslope_sub_smul_of_ne` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/DSlope.lean`: theorem dslope_sub_smul_of_ne (f : 𝕜 → E) (h : b ≠ a) :

### statement-generality: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L56-L61)

Declaration: `LimitRepresentation.smoothPeriodicTest_memL2On (and downstream smoothPeriodicTestL2, weakPathRepresentative_pairing_eq_inner, FrozenDriftProblem.initial_pairing_eq_cell_integral, weakPathRepresentative_testPairing_continuous)`

The hypothesis `ContDiff ℝ ⊤ ψ` is stronger than the proof uses. The proof only uses `hψ.continuous`, through measurability and continuity of `ψ^2` on the compact closed cell. The torus class `smoothPeriodicTestL2` is built only from this `MemL2On` fact. `weakPathRepresentative_pairing_eq_inner`, `initial_pairing_eq_cell_integral` and `weakPathRepresentative_testPairing_continuous` use `hψ` only through these two declarations, so smoothness plays no role in any of them. All of them are therefore stated for smooth tests when they hold for any continuous periodic test.

Proposed change:

State the lemma for a continuous function: `theorem LimitRepresentation.continuousPeriodicTest_memL2On {ψ : Vec 2 → ℝ} (hψ : Continuous ψ) : MemL2On AVenhance.unitCube ψ`. The proof is the same with `hψ` in place of `hψ.continuous`. Then either take `(hψ : Continuous ψ)` in `smoothPeriodicTestL2` and in the three downstream theorems, or keep the smooth-input versions as one-line wrappers using `hψ.continuous`. The downstream proofs would not change, because they only call `smoothPeriodicTest_memL2On hψ` and `smoothPeriodicTestL2 hψ hperiodic`.

Benefit: Users can pair the weak path with continuous periodic tests, for example a mollification-free limit argument, a test built from a merely continuous coefficient, or density arguments in C⁰. They do not have to supply an unneeded smoothness proof. The statement also records that only continuity is needed for the pairing identity and the time-continuity result.

Source evidence:

- `LimitRepresentation.smoothPeriodicTest_memL2On` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: (hψ.continuous.pow 2).continuousOn.integrableOn_compact
- `frozenInitialData_memLp_torus` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/FrozenInitialData.lean`: (hθ₀ : MemL2On AVenhance.unitCube θ₀) :
- `smoothPeriodicTestL2` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: (frozenInitialData_memLp_torus (LimitRepresentation.smoothPeriodicTest_memL2On hψ)).toLp

### statement-generality: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L45-L145)

Declaration: `planeCurveToBivariate (and companion lemmas planeCurveToBivariate_X_zero/_X_one/_C, planeCurveToBivariate_natDegree_eq_degreeOf_zero, bivariateEquiv_symm_natDegree_eq_degreeOf_one)`

The plane-curve/bivariate conversion and its coordinate and degree lemmas are stated for an arbitrary field `K`. Their proofs use only `MvPolynomial.finSuccEquiv`, `Polynomial.mapAlgEquiv`, `MvPolynomial.uniqueAlgEquiv`, `MvPolynomial.optionEquivLeft`, `Polynomial.Bivariate.equivMvPolynomial`, `natDegree_map_eq_of_injective` and `degreeOf_eq_natDegree`. Mathlib states all of these for `CommSemiring`. The `Field` assumption is never used by any of these declarations. It also makes the file inconsistent, because the neighbouring `degreeOf_map_eq_of_injective` is already stated for `CommSemiring`.

Proposed change:

Change the binder to `(K : Type*) [CommSemiring K]` for `planeCurveToBivariate`, `planeCurveToBivariate_X_zero`, `_X_one`, `_C`, `planeCurveToBivariate_natDegree_eq_degreeOf_zero` and `bivariateEquiv_symm_natDegree_eq_degreeOf_one`. Their proofs should go through unchanged: `MvPolynomial.finSuccEquiv`, `MvPolynomial.natDegree_finSuccEquiv` and `Polynomial.Bivariate.equivMvPolynomial` are all stated over `CommSemiring`. Keep `transposeBivariate_planeCurveToBivariate` and the downstream lemmas at `Field`, since `transposeBivariate` is defined with `[Field C]`. Optionally, generalise `transposeBivariate` too, since it only uses `Polynomial.eval₂RingHom`, `mapRingHom` and `C`, none of which needs a field.

Benefit: The iterated-polynomial presentation and the coordinate-degree identities become reusable for `ℤ`, `ZMod n`, polynomial rings and other base rings. Examples are integral models of the curve and rings of constants that are not fields. Users get fewer artificial field-specialisation obstacles, and the file's generality becomes consistent with `degreeOf_map_eq_of_injective`. This is a weakened typeclass assumption, with the same intended mathematics for fields.

Source evidence:

- `Polynomial.Bivariate.equivMvPolynomial` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Polynomial/Bivariate.lean`: def equivMvPolynomial : R[X][Y] ≃ₐ[R] MvPolynomial (Fin 2) R :=
- `MvPolynomial.natDegree_finSuccEquiv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/MvPolynomial/Equiv.lean`: theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).natDegree = degreeOf 0 f := by
- `degreeOf_map_eq_of_injective` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: {R S σ : Type*} [CommSemiring R] [CommSemiring S]

### statement-generality: [LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L46-L52)

Declaration: `EulerMeanHarmonic.norm_add_sq_le_twice`

The statement is a pure triangle-inequality fact about norms, but it is stated only for the concrete `Space` (EuclideanSpace ℝ (Fin 3)). The proof uses only `norm_add_le`, `norm_nonneg` and `sq_nonneg`, so it holds in any seminormed additive group. The specialisation prevents reuse for other value spaces, such as scalar fields or other Euclidean spaces, and hides the fact that no geometry of ℝ³ is involved.

Proposed change:

State it for an arbitrary seminormed group: `theorem norm_add_sq_le_twice {E : Type*} [SeminormedAddCommGroup E] (a b : E) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2`. The proof body should work unchanged: `norm_add_le a b` gives ‖a+b‖ ≤ ‖a‖+‖b‖, the norms are nonnegative, and `nlinarith [sq_nonneg (‖a‖-‖b‖)]` closes the goal. The only call site, `norm_add_sq_le_twice (u x) (v x)` at line 64, elaborates as before with E := Space. The degenerate case a = b = 0 is covered by the same proof.

Benefit: The lemma becomes a reusable general inequality, such as a parallelogram-type bound for any normed space. Downstream L²-type estimates over other target spaces then don't need to re-prove it. It also states more clearly that only the triangle inequality is used.

Source evidence:

- `EulerMeanHarmonic.norm_add_sq_le_twice` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean`: have h := norm_add_le a b
- `EulerMeanHarmonic.localL2Energy_add_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean`: exact norm_add_sq_le_twice (u x) (v x)

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

### vacuity-and-misstatement: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L371-L380)

Declaration: `VectorBundle`

The docstring does not match the class. It says the total space has a 'topological vector space structure' and that the condition is the existence of a linear trivialization around every point. The class `VectorBundle` instead requires two things: every trivialization in the atlas is fiberwise linear (`trivialization_linear'`), and `coordChangeL` is continuous in the operator-norm topology on the overlaps (`continuousOn_coordChange'`). The second condition is not mentioned in the docstring, even though it is the substantive condition (the module docstring does state it). Mere existence of linear local trivializations around each point would not imply it. The total space is also not a vector space, only a bundle of vector spaces. The docstring also says each fiber is a 'topological vector space', but the typeclass assumptions are only `AddCommMonoid`, `Module` and `TopologicalSpace` on `E x`.

Proposed change:

Reword the docstring to say that `VectorBundle R F E` states that `E` is a fiber bundle whose trivializations in the atlas are all fiberwise `R`-linear and whose coordinate changes `Trivialization.coordChangeL R e e'` are continuous on `e.baseSet ∩ e'.baseSet` for the operator-norm topology on `F →L[R] F`. Drop the phrase 'topological vector space structure' on the total space.

Benefit: A reader sees the real hypotheses. In particular, they see that linear local trivializations alone are not enough and that continuity of the transition maps is also required.

Source evidence:

- `VectorBundle` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: continuousOn_coordChange' :
    ∀ (e e' : Trivialization F (π F E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e'],

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

### vacuity-and-misstatement: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L513-L513)

Declaration: `planeCurve_auxiliaryFamily_linearIndependent_of_absoluteIrreducible_coordinateDegrees (and the chain planeCurve_auxiliaryFamily_linearIndependent, _of_nonzero_partials, _of_absoluteIrreducible)`

The hypothesis `∂₁ f ≠ 0` is never used. In the main theorem it is literally named `_hpartialSecond`, and its proof never mentions it. The later wrappers only pass it down to that theorem. Separability over the second coordinate, the Frobenius exclusion and the minimal-polynomial degree all come from `hpartialFirst` alone, through `finiteSeparable_over_secondCoordinate_of_irreducible hf hpartialFirst` and `secondCoordinate_not_mem_frobeniusSubfield`. The theorems therefore state a strictly weaker result than what is proved. They exclude absolutely irreducible curves with `∂₁ f = 0` (those with `f` a polynomial in `y^p`) although the conclusion holds for them. The names `_of_nonzero_partials` and the doc "two separating-coordinate hypotheses" suggest both partials are mathematically needed, which they are not.

Proposed change:

Drop `hpartialSecond` from `planeCurve_auxiliaryFamily_linearIndependent` and from the three wrappers, so that only `hpartialFirst` remains. If a symmetric statement is wanted for fidelity to the source, add it as a separate corollary. Alternatively, state in the docstrings that the hypothesis is unused and kept only for the source's shape.

Benefit: The results apply to a strictly larger class of curves. The hypotheses then record what is actually used, so a reader is not led to believe the second separating coordinate plays a role in the argument.

Source evidence:

- `planeCurve_auxiliaryFamily_linearIndependent` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: (_hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
- `planeCurve_auxiliaryFamily_linearIndependent` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: finiteSeparable_over_secondCoordinate_of_irreducible hf hpartialFirst

### vacuity-and-misstatement: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L327-L334)

Declaration: `planeCurve_auxiliaryFamily_linearIndependent (docstring)`

The docstring says that `hbaseChange` and `hsecondNotFrobenius` are exact geometric boundaries that are not hidden. It calls `hsecondNotFrobenius` the "missing differential/basis compatibility". But `hsecondNotFrobenius` follows from `hpartialFirst` and `hf`, by `secondCoordinate_not_mem_frobeniusSubfield`, which this file uses at lines ~407-412 in `_of_nonzero_partials`. So it is not an extra geometric assumption. It is a redundant hypothesis, and the "missing" compatibility is already proved. Likewise `hbaseChange` is derived from absolute irreducibility in the last two theorems. The comment misdescribes the strength of the theorem, because it implies that the statement depends on an unproved input.

Proposed change:

Rewrite the docstring to say that `hsecondNotFrobenius` is redundant given `hpartialFirst`, and that the user-facing theorem is `_of_nonzero_partials`. State that `hbaseChange` is the only genuinely extra irreducibility input, and that it is discharged by `_of_absoluteIrreducible`. Alternatively, make this theorem `private` or rename it as an internal step.

Benefit: Readers get an accurate account of which assumptions are real boundaries. They also avoid the false impression that the Frobenius exclusion is an open gap.

Source evidence:

- `secondCoordinate_not_mem_frobeniusSubfield` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/SeparatingCoordinateNotFrobenius.lean`: planeCurveFunction f 1 ∉
      frobeniusSubfield (PlaneCurveFunctionField f) p := by
- `planeCurve_auxiliaryFamily_linearIndependent_of_nonzero_partials` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: (secondCoordinate_not_mem_frobeniusSubfield
        (p := p) hf hpartialFirst)

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

### missing-structure: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L45-L66)

Declaration: `Algebra.TensorProduct.basisAux / basisAux_map_smul / basis`

The docstring of `basisAux` says the equivalence is "in fact `A`-linear". The definition is only an `R`-linear equivalence `≃ₗ[R]`. The `A`-linearity is proved separately as the unbundled lemma `basisAux_map_smul`. `basis` then builds its `repr` by hand, re-bundling the `R`-linear equivalence with `map_smul'`. The A-linear equivalence `A ⊗[R] M ≃ₗ[A] (ι →₀ A)` is the mathematically natural object. It is never exposed, and `basisAux` is not used outside this file.

Proposed change:

Make `basisAux A b` an `A ⊗[R] M ≃ₗ[A] ι →₀ A`. Keep the current underlying equivalence and prove `map_smul'` inside the definition using the current `basisAux_tmul`-based argument. Then drop `basisAux_map_smul` as a public lemma. `basis` becomes `Basis.ofRepr (basisAux A b)` (or `⟨basisAux A b⟩`), and `basis_repr_tmul` follows from `basisAux_tmul` unchanged. If the `R`-linear form is still wanted, it can be recovered with `LinearEquiv.restrictScalars R`.

Benefit: The `A`-module structure is stated in the type, so the docstring caveat and the manual `{ ... with map_smul' := ... }` repackaging go away. The equivalence also gets the generic `LinearEquiv` API over `A`, such as `symm`, `trans` and `map_smul`. Callers no longer need a separate preservation lemma.

Source evidence:

- `Algebra.TensorProduct.basisAux_map_smul` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: theorem basisAux_map_smul (a : A) (x : A ⊗[R] M) : basisAux A b (a • x) = a • basisAux A b x
- `Algebra.TensorProduct.basisAux` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: noncomputable def basisAux : A ⊗[R] M ≃ₗ[R] ι →₀ A :=

### missing-structure: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L145-L154)

Declaration: `ZMod.rootsOfUnityAddChar / bijective_rootsOfUnityAddChar / surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar`

The file builds the `AddChar` `ZMod.rootsOfUnityAddChar n` and then proves that it is bijective, with a helper that states surjectivity of the composite `rootsOfUnityCircleEquiv n ∘ ZMod.rootsOfUnityAddChar n`. The resulting isomorphism ZMod n ≅ rootsOfUnity n Circle is only a `Bijective` fact about a coerced function. It is not packaged as an `AddEquiv`/`MulEquiv`. The composite with `rootsOfUnityCircleEquiv` into `rootsOfUnity n ℂ` is also an unbundled function composition, even though it is again an additive character.

Proposed change:

Bundle the bijection as an equivalence. For example, apply `AddEquiv.ofBijective` to `(ZMod.rootsOfUnityAddChar n).toAddMonoidHom`, which has type `ZMod n →+ Additive (rootsOfUnity n Circle)`. Or use `MulEquiv.ofBijective` on `.toMonoidHom`. Name the result something like `ZMod.rootsOfUnityAddEquiv`. Keep `bijective_rootsOfUnityAddChar` as the proof of its bijectivity argument. Define the complex-valued version as `(rootsOfUnityCircleEquiv n).toMonoidHom.compAddChar (ZMod.rootsOfUnityAddChar n)`, if such a composition lemma is wanted, in place of the `∘` statement.

Benefit: Users get an `AddEquiv`/`MulEquiv` with `symm`, `trans` and `map_add` API, and no longer have to rebuild one from `Bijective` with `Equiv.ofBijective`. This is the natural form for identifying `ZMod n` with the n-th roots of unity, for example when transferring `HasEnoughRootsOfUnity` or counting characters. The composite surjectivity lemma becomes simple lemmas about `MulEquiv.comp`.

Source evidence:

- `AddChar.toAddMonoidHom` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Algebra/Group/AddChar.lean`: def toAddMonoidHom (φ : AddChar A M) : A →+ Additive M where
- `MulEquiv.ofBijective` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Algebra/Group/Equiv/Defs.lean`: noncomputable def ofBijective {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
- `ZMod.rootsOfUnityAddChar` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: AddChar (ZMod n) (rootsOfUnity n Circle) where

### missing-structure: [TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean#L513-L556)

Declaration: `LinearMap.taylorComponent (with taylorComponent_zero / taylorComponent_add / taylorComponent_smul)`

taylorComponent b n is b ↦ (letter ∘ₗ b) ∘ₗ of n, which is linear in b. The file states this as three separate preservation lemmas (zero, add, smul) about an unbundled function. It therefore gets none of the LinearMap API, such as map_sum, map_neg, map_sub, or composition with the coderivEquivTaylor map. taylorComponent_add and taylorComponent_smul are not used anywhere in the repo. taylorComponent_zero is used in only two places.

Proposed change:

Bundle the map: define the linear map (ReducedTensorWords R M →ₗ[R] ReducedTensorWords R M) →ₗ[R] ((n : {n : ℕ // 0 < n}) → TensorPower R n.1 M →ₗ[R] M) as Pi.lift/LinearMap.pi of (LinearMap.lcomp-style) postcomposition with letter via LinearMap.compRight (letter R M) and precomposition with `of R M n`. Keep the pointwise `taylorComponent_apply` as a simp lemma. Then drop the zero/add/smul lemmas and use map_zero, map_add, map_smul and map_sum. Alternatively, keep the arity-wise function but define it from `LinearMap.compRight`/`LinearMap.lcomp` so linearity is inherited.

Benefit: Linearity becomes a single structured fact, and generic lemmas apply directly. Statements such as eq_zero_iff_taylorComponent_eq_zero become injectivity/kernel statements about a bundled linear map. This also matches the already bundled coderivEquivTaylor.

Source evidence:

- `LinearMap.compRight` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Algebra/Module/LinearMap/End.lean`: def compRight (f : M₁ →ₗ[R] M₂) : (M →ₗ[R] M₁) →ₗ[S] M →ₗ[R] M₂ where
- `LinearMap.taylorComponent` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/TensorCoalgebra/Coderivation.lean`: (letter R M ∘ₗ b) ∘ₗ of R M n

### missing-structure: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L324-L331)

Declaration: `TauCeti.exists_normalDisc`

The docstring says ψ z is a family of linear isometries from ℂ onto the normal plane. The statement exposes ψ z only as a bare function ℂ → ℝ³. It records the isometry, injectivity, range and onto-the-normal-plane properties as four separate hypotheses. Linearity is not stated, even though ψ z w = re w • n₁ z + im w • n₂ z is ℝ-linear. Injectivity is redundant, since it follows from the norm identity once ψ z is linear. The consumer `exists_isSolidTorusNeighborhood` re-derives norm facts by hand (`hnorm` uses `(hψ q.2).2.1`) and pulls injectivity out as `(hψ _).2.2.1`.

Proposed change:

State the result with a bundled map, for example `∃ ψ : Circle → ℂ →ₗᵢ[ℝ] ℝ³, Continuous (fun q : SolidTorus => ψ q.2 q.1) ∧ ∀ z, (∀ w, ψ z w ∈ normalSubspace (𝓡 1) f z) ∧ ∀ v ∈ normalSubspace (𝓡 1) f z, ∃ w, ψ z w = v`. Equivalently, say `LinearMap.range (ψ z).toLinearMap = normalSubspace (𝓡 1) f z`. Build `ψ z` from the frame, for instance as the linear isometry that sends the basis `1, I` to `n₁ z, n₂ z`. The `Complex.orthonormalBasisOneI` / `Complex.isometryOfOrthonormal` API is the natural route. The norm identity then follows from `LinearIsometry.norm_map`, and injectivity from `LinearIsometry.injective`. The uses of `(hψ z).2.1` and `(hψ _).2.2.1` in `exists_isSolidTorusNeighborhood` become `(ψ z).norm_map` and `(ψ z).injective`. The manual `sq_eq_sq₀` / `normSq_apply` / `Complex.ext` computations in the proof of this lemma are replaced by one construction of the isometry. Only the continuity statement stays about the unbundled function `fun q => ψ q.2 q.1`.

Benefit: The statement matches its docstring and the geometric meaning, a linear isometry from ℂ onto the normal plane. The redundant injectivity field and the hand-written norm identities go away. Callers get the existing `LinearIsometry` API (`norm_map`, `injective`, `range`, composition with scalar multiplication) instead of re-deriving it.

Source evidence:

- `TauCeti.exists_isSolidTorusNeighborhood` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: rw [norm_smul, (hψ q.2).2.1, Real.norm_of_nonneg hr.le]
- `TauCeti.exists_isSolidTorusNeighborhood` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: exact Prod.ext (Subtype.ext ((hψ _).2.2.1 (smul_right_injective _ hr.ne' h₁))) h₂
- `Complex.isometryOfOrthonormal` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Analysis/InnerProductSpace/PiL2.lean`: def Complex.isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) : ℂ ≃ₗᵢ[ℝ] F :=

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

### missing-structure: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L219-L257)

Declaration: `evalBivariate_planeCurveFrobeniusRelation`

`evalBivariate u v` is an unbundled function. It is defined as `P.eval₂ (Polynomial.eval₂RingHom (algebraMap C L) u) v`, and it is a ring homomorphism, or an algebra homomorphism over `C`. This proof therefore rebuilds the same ring homomorphism by hand as the local `evalIterated`. It then proves `lhs = rhs` by `ringHom_ext` and unfolds the `simp only [...evalIterated...]` steps. The bundled version already exists in the library as `bivariateEvalAlgHom`, with `bivariateEvalAlgHom_eq_evalBivariate` proved by `rfl`.

Proposed change:

Use the existing bundled map instead of the local `evalIterated`. For example, take `bivariateEvalAlgHom (K := F) y x` (as a RingHom via `.toRingHom`). Alternatively, define a bundled `evalBivariateHom` upstream, next to `evalBivariate`, and state this theorem with it. The proof would then compare two bundled composites on `MvPolynomial (Fin 2) K`. If `PoweredImageFrobeniusRelation` cannot be imported without a cycle, move or generalize `bivariateEvalAlgHom` to the earlier file that defines `evalBivariate`.

Benefit: It removes the duplicated local construction and the `simp only [... evalIterated ...]` unfolding. The evaluation lemma then uses the same API that downstream files (`PoweredImageBaseChange`) already use for `bivariateEvalAlgHom_comp`. The result becomes a composition of bundled maps, which can be reused for other base changes.

Source evidence:

- `evalBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/AuxiliaryFamily.lean`: def evalBivariate (u v : L) (P : Polynomial (Polynomial C)) : L :=
  P.eval₂ (Polynomial.eval₂RingHom (algebraMap C L) u) v
- `bivariateEvalAlgHom` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PoweredImageFrobeniusRelation.lean`: Polynomial (Polynomial K) →ₐ[K] A :=
  Polynomial.eval₂AlgHom (Polynomial.aeval u) v (fun _ ↦ Commute.all _ _)
- `bivariateEvalAlgHom_eq_evalBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PoweredImageFrobeniusRelation.lean`: bivariateEvalAlgHom (K := K) u v P = evalBivariate u v P := by
  rfl

### missing-structure: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L187-L192)

Declaration: `planeCurveFrobeniusRelation`

`planeCurveFrobeniusRelation` is a bare function. It is the composite of two bundled maps: `MvPolynomial.map ι` with `ι := perfectConstantsToFrobeniusSubfield`, and the AlgEquiv `planeCurveToBivariate`. Each property is then proved separately: degree preservation, transposed degree, evaluation and irreducibility. The evaluation lemma (lines 219–257) and `transposeBivariate_planeCurveToBivariate` (lines 117–134) each build `lhs` and `rhs` ring homomorphisms by hand and use `ringHom_ext`. The irreducibility lemma re-invokes `.map ... toMulEquiv` on the composite. Because the relation is not itself a hom, its structure (a ring homomorphism `MvPolynomial (Fin 2) K →+* Polynomial (Polynomial F)`) is not visible to `simp` or to generic `map_*` lemmas.

Proposed change:

Define a bundled map, for example `planeCurveFrobeniusHom : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial (frobeniusSubfield L p))` as `(planeCurveToBivariate _).toRingEquiv.toRingHom.comp (MvPolynomial.map ι)`. Define `planeCurveFrobeniusRelation f` as its value at `f`, or make the existing lemmas statements about the hom. Then the evaluation lemma becomes a comparison of two bundled homs, using `ringHom_ext` once. Multiplicativity, additivity and `map_pow` are free for any later use on products or powers of plane equations.

Benefit: Readers and downstream users get `map_mul`, `map_add` and composition lemmas for the base-changed relation without re-proving them. Extending to a pipeline over other base changes also becomes easier. The cost is small because the underlying pieces are already bundled.

Source evidence:

- `perfectConstantsToFrobeniusSubfield` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PerfectConstants.lean`: def perfectConstantsToFrobeniusSubfield : K →+* frobeniusSubfield L p :=
- `planeCurveToBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
- `evalBivariate_planeCurveFrobeniusRelation` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`:   let lhs : MvPolynomial (Fin 2) K →+* L :=
    evalIterated.comp

### simp-interface: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L83-L89)

Declaration: `DFinsupp.singleton / DFinsupp.mem_singleton_apply_iff`

The bundled `DFinsupp.singleton` has no `rfl` application lemma, although the sibling `rangeIcc` has the simp lemma `rangeIcc_apply`. Because `singleton` is a plain def, `simp` cannot rewrite `f.singleton i` to `{f i}`. The only available lemma, `mem_singleton_apply_iff`, is not tagged simp. So `a ∈ f.singleton i` does not normalise to `a = f i`. Only that membership form can be rewritten by hand with the lemma, and the apply form `⇑(f.singleton) i` is stuck.

Proposed change:

Add `@[simp] theorem singleton_apply (f : Π₀ i, α i) (i : ι) : f.singleton i = {f i} := rfl`, mirroring `rangeIcc_apply`. With it, `mem_singleton_apply_iff` follows by `simp` through `Finset.mem_singleton`. Alternatively, mark `mem_singleton_apply_iff` as simp. The normal form is `{f i}`, then `a = f i`, and neither rule can loop.

Benefit: Goals that mention `f.singleton i` or `a ∈ f.singleton i` simplify automatically, as they do for `rangeIcc`. This makes the two bundled-finset constructors consistent, and users no longer have to unfold `singleton` by hand.

Source evidence:

- `DFinsupp.rangeIcc_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: theorem rangeIcc_apply (f g : Π₀ i, α i) (i : ι) : f.rangeIcc g i = Icc (f i) (g i) := rfl

### simp-interface: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L245-L247)

Declaration: `Bundle.Trivialization.linearMapAt_def_of_notMem (and Pretrivialization.linearMapAt_def_of_notMem / linearMapAt_eq_zero)`

The simp interface for the extended-by-zero maps is asymmetric. For `symmₗ` and `symmL` there are simp lemmas for both cases (`symmₗ_apply_of_notMem`, `symmL_apply_of_notMem`, alongside the `_apply` lemma for `b ∈ baseSet`). For `linearMapAt`, only the in-base-set case `coe_linearMapAt_of_mem` is `@[simp]`. The off-base-set case `linearMapAt_def_of_notMem` is not simp, so `e.linearMapAt R b y` with `hb : b ∉ e.baseSet` in context is not reduced to `0`. `continuousLinearMapAt` has no off-base-set rule either, and its simps lemma only rewrites it to `linearMapAt`. The Pretrivialization section also states the same fact twice (`linearMapAt_def_of_notMem` and `linearMapAt_eq_zero`, both `= 0` by `dite_eq_right hb`), none tagged simp.

Proposed change:

Mark the Trivialization (and Pretrivialization) `linearMapAt_def_of_notMem` as `@[simp]`. It is oriented `linearMapAt R b = 0`, has the hypothesis `b ∉ e.baseSet`, which simp can discharge from context, and cannot loop. Optionally add a matching `continuousLinearMapAt_of_notMem` simp lemma. Drop the duplicate `linearMapAt_eq_zero` or make it the single canonical name.

Benefit: Users can simplify the zero-extended fiber maps outside the base set the same way they already do for `symmₗ` and `symmL`. They no longer need to unfold via `linearMapAt_apply` and `if_neg` by hand, and the near-duplicate lemmas stop competing for the same role.

Source evidence:

- `Bundle.Trivialization.symmL_apply_of_notMem` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: lemma symmL_apply_of_notMem (e : Trivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) (y : F) : e.symmL R b y = 0 :=
- `Bundle.Pretrivialization.linearMapAt_eq_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: theorem linearMapAt_eq_zero (e : Pretrivialization F (π F E)) [e.IsLinear R] {b : B}
    (hb : b ∉ e.baseSet) : e.linearMapAt R b = 0 :=

### simp-interface: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L720-L722)

Declaration: `VectorBundleCore.localTrivAt_def together with localTriv_continuousLinearMapAt, localTriv_symmL, localTriv_symm_apply, localTriv_coordChange_eq`

`localTrivAt_def` is a simp/mfld_simps rewrite of `Z.localTriv (Z.indexAt b)` to `Z.localTrivAt b`. `localTrivAt` is an ordinary (non-reducible) def. The simp lemmas stated for `Z.localTriv i` are `localTriv_continuousLinearMapAt`, `localTriv_symmL`, `localTriv_symm_apply`, `localTriv_coordChange_eq` and `mem_localTriv_source`. For an expression like `(Z.localTriv (Z.indexAt b₀)).continuousLinearMapAt R b`, simp visits the subterm first, rewrites it to `Z.localTrivAt b₀`, and the outer lemma probably no longer matches because `Z.localTriv ?i` cannot be unified with `Z.localTrivAt b₀` at simp's transparency. There are `trivializationAt_*` versions of these lemmas, but no `localTrivAt_*` versions of continuousLinearMapAt, symmL or coordChange. This is untested, and the unification claim is from reading the definitions.

Proposed change:

Either add `localTrivAt_continuousLinearMapAt` and `localTrivAt_symmL` simp lemmas (and a coordChange analogue), each stated with `Z.localTrivAt b₀`, proved by `Z.localTriv_continuousLinearMapAt hb` etc. Or drop `simp` from `localTrivAt_def` and keep `localTriv (indexAt b)` as the normal form, with the `trivializationAt_*` lemmas covering the other side.

Benefit: This gives a single canonical normal form, so the VectorBundleCore simp lemmas apply to the preferred trivialization `localTrivAt b₀` (which `trivializationAt` unfolds to). The coordinate-change, `symmL` and `continuousLinearMapAt` rules would no longer depend on which spelling simp reaches first.

Source evidence:

- `VectorBundleCore.localTriv_continuousLinearMapAt` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: (Z.localTriv i).continuousLinearMapAt R b = Z.coordChange (Z.indexAt b) i b
- `VectorBundleCore.trivializationAt_symmL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: (trivializationAt F Z.Fiber b₀).symmL R b = Z.coordChange (Z.indexAt b₀) (Z.indexAt b) b
- `FiberBundleCore.localTrivAt_def` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/FiberBundle/Basic.lean`: theorem localTrivAt_def (b : B) : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=

### simp-interface: [Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L350-L356)

Declaration: `CliffordAlgebra.equivExterior`

`@[simp]` on a `def` makes simp unfold `equivExterior Q` into `changeFormEquiv changeForm.associated_neg_proof`. That exposes the implementation instead of giving a stable normal form in terms of `equivExterior`. The simp set is only usable through the unfolding. The simpNF linter fails on the generated `equivExterior.eq_1`, which is why `attribute [nolint simpNF] equivExterior.eq_1` and an adaptation note are needed. The one downstream use, `(by simp)` in Inversion.lean, depends on this unfolding followed by `changeFormEquiv_apply` and `changeForm_algebraMap`.

Proposed change:

Remove `@[simp]` from `equivExterior` and the `nolint simpNF` attribute. Add targeted simp lemmas about the abstract equivalence, for example one for `equivExterior Q (algebraMap R _ r)`, one for `equivExterior Q (ι Q m)`, and perhaps `equivExterior_apply` stating `equivExterior Q x = changeForm changeForm.associated_neg_proof x`. These can be proved by `changeForm_algebraMap` and `changeForm_ι`. Then change the `by simp` in Inversion.lean to use them (or `simp [equivExterior]`).

Benefit: Users get a stable simp normal form that keeps `equivExterior` opaque, and the unexplained linter suppression goes away. simp no longer exposes `changeFormEquiv` and the `associated_neg_proof` term in goals about `equivExterior`.

Source evidence:

- `CliffordAlgebra.invertibleOfInvertibleι` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Inversion.lean`: .algebraMapOfInvertibleAlgebraMap (equivExterior Q).toLinearMap (by simp)
- `CliffordAlgebra.changeForm_algebraMap` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: theorem changeForm_algebraMap (r : R) : changeForm h (algebraMap R _ r) = algebraMap R _ r

### simp-interface: [Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L186-L195)

Declaration: `CliffordAlgebra.contractLeft_contractLeft / contractRight_contractRight`

The sibling normalisation lemmas `contractLeft_ι`, `contractLeft_algebraMap`, `contractLeft_one` and their right-hand versions are `@[simp]`. The square-zero identities `d⌋(d⌋x) = 0` and `x⌊d⌊d = 0` are not. They reduce a term to `0`, have no cycle risk, and need no hypotheses. A goal containing a repeated contraction is therefore not simplified. The file's own uses spell the rewrite out with `rw [..., contractLeft_contractLeft, ...]` in `changeFormAux_changeFormAux`. `contractLeft_comm` is correctly not simp, because it would loop or permute.

Proposed change:

Mark `contractLeft_contractLeft` and `contractRight_contractRight` as `@[simp]`. Leave `contractLeft_comm` and `contractRight_comm` non-simp.

Benefit: Repeated contractions by the same functional collapse to `0` automatically, matching the other contraction lemmas in the simp set. This should let proofs like `changeFormAux_changeFormAux` use `simp` instead of an explicit `rw` chain. I could not test whether it does.

Source evidence:

- `CliffordAlgebra.changeFormAux_changeFormAux` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: sub_self, sub_zero, contractLeft_contractLeft, add_zero, sub_smul]
- `CliffordAlgebra.contractLeft_one` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: theorem contractLeft_one : d⌋(1 : CliffordAlgebra Q) = 0 := by

### simp-interface: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L89-L89)

Declaration: `ZMod.stdAddChar_apply`

`stdAddChar_apply` is the canonical unfolding of `stdAddChar` to `toCircle`. It is not tagged `@[simp]`, so every user has to name it explicitly. Three downstream proofs do this: `simp only [dft_apply, stdAddChar_apply, ...]` in Analysis/Fourier/ZMod.lean, `simp only [sum_mul, mul_sum, smul_eq_mul, stdAddChar_apply, ← mul_assoc]` in LSeries/ZMod.lean, and a `rw [..., stdAddChar_apply, ...]` in Fourier/ZMod.lean. The interface also has two other normal forms for the same term. `stdAddChar_coe` rewrites `stdAddChar (j : ZMod N)` to an explicit `exp`. The `AddChar.compAddMonoidHom_apply` route used by `toCircle_intCast` rewrites it the other way. Nothing says which form simp should produce.

Proposed change:

Decide on one normal form and record it. Either mark `stdAddChar_apply` `@[simp]` (the RHS is a bare coercion of a character value, so the rewrite terminates), or add a docstring saying it is deliberately left non-simp. If the attribute is added, the `simp only [..., stdAddChar_apply, ...]` call sites could use plain `simp`, though I have not checked that they would still close.

Benefit: Readers and users of `stdAddChar` get one canonical form (`↑(toCircle j)`) from simp, and downstream proofs no longer have to remember to pass this lemma by name.

Source evidence:

- `line 218 (simp only call)` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/NumberTheory/LSeries/ZMod.lean`: simp only [sum_mul, mul_sum, smul_eq_mul, stdAddChar_apply, ← mul_assoc]
- `line 138 (simp only call)` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/Fourier/ZMod.lean`: simp only [dft_apply, stdAddChar_apply, Fourier.fourierIntegral_def

### simp-interface: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L140-L143)

Declaration: `ZMod.toCircle_natCast / rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val`

The proof reverses `toCircle_natCast` (`← ZMod.toCircle_natCast`) and removes the simp lemma `ZMod.natCast_val` (`-ZMod.natCast_val`) by hand. It then re-adds `ZMod.natCast_zmod_val` to cancel the cast of `j.val`. That is a sign that the interface for `toCircle` applied to a casted `ZMod.val` is awkward. `toCircle_natCast` has the cast on the left and `exp (2 * π * I * j / N)` on the right, and the file uses it in both directions: backwards at line 143 and forwards at line 148, where `simp [..., ZMod.toCircle_natCast, mul_div_assoc]` needs `mul_div_assoc` to match the shape. The `exp (2 * π * I * ↑j.val / ↑N)` form produced by `toCircle_apply` is the same expression that `ZMod.natCast_val` would rewrite, so the two collide.

Proposed change:

State the evaluation lemma for the `exp` side in the form the downstream proofs consume, and give it a purpose-built simp lemma. One option is a lemma `(toCircle j : ℂ) = exp (2 * π * I * j.val / N)` (the coercion of `toCircle_apply`) with a `@[simp]` or `@[simp, norm_cast]` attribute, so that line 143 reduces to `simp`. Alternatively, restate `rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val` with the `ZMod.cast`-free `toCircle` value and drop the `-ZMod.natCast_val` argument.

Benefit: Removes the manual simp-set surgery and the back-and-forth use of `toCircle_natCast`. The proofs become robust if `ZMod.natCast_val` changes, and a new reader does not have to work out why that lemma is excluded.

Source evidence:

- `surjective_rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: simp [Units.ext_iff, Subtype.ext_iff, ← hj2, ZMod.toCircle_natCast, mul_div_assoc]
- `ZMod.toCircle_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: rw [← toCircle_natCast, natCast_zmod_val]

### simp-interface: [TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L98-L100)

Declaration: `Matrix.SpecialOrthogonalGroup.mem_center_iff`

The lemma is tagged `@[simp]`, but it is a conditional characterization of center membership. Its left side is `g ∈ Subgroup.center (specialOrthogonalGroup n R)`. Its right side is an existential with a scalar equation and two power conditions. The hypotheses `IsRegular (2 : R)` and `3 ≤ Fintype.card n` are non-propositional-trivial side conditions. Simp generally cannot discharge them for a generic ring or index type. Where it can, the rewrite replaces a compact membership predicate with a larger `∃ c, ... ∧ ... ∧ ...` formula, so the result is not a canonical normal form. It also competes with the generic `Subgroup.mem_center_iff` and related simp rules. The only use in the repository, in `eq_one_of_mem_center_of_odd`, applies it explicitly with `(mem_center_iff h2 g hn).mp hg` and does not rely on simp. Elsewhere, `simp` on a center-membership goal may expand it or fail to fire.

Proposed change:

Remove `@[simp]` from `mem_center_iff` and leave it as a plain iff for explicit `rw` or `.mp` use. If a simp-normal form is wanted, add a separate unconditional lemma for a concrete expression. For example, a lemma `scalar n c ∈ center` stated for a scalar matrix with `c ^ 2 = 1` and `c ^ card n = 1` could be proved from `mem_center_of_coe_eq_scalar`.

Benefit: This avoids an unintended expansion of center membership into an existential. It avoids competition with the generic center lemmas and a lemma that simp can rarely apply because of its side conditions. Downstream simp calls stay predictable. The explicit uses are unaffected.

Source evidence:

- `Matrix.SpecialOrthogonalGroup.eq_one_of_mem_center_of_odd` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean`: (mem_center_iff h2 g hn).mp hg

### simp-interface: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L91-L98)

Declaration: `TauCeti.schwarzChristoffelBoundary_apply_prevertex`

The lemma is `@[simp]` but has a hypothesis `-1 < ∑ i with a i = a j, e i`. The simp discharger can only prove it if that exact inequality, or something rewriting to it, is in the simp set or the local context. For arbitrary `a`, `e`, `j` it is a substantive analytic condition, so a bare `simp` will usually leave the rewrite unfired. Every use in the repository passes `he`/`hj`/`hfinite _` explicitly, e.g. via `rw [...]`, `← ...`, `simpa only [...]`, or `simpa [schwarzChristoffelBoundary_apply_prevertex a e z₀ j he]`. None of them relies on the attribute. Nothing in the repository depends on the attribute, and it suggests a normal form `boundary (a j) ↦ vertex` that simp cannot deliver in general. The statement's LHS also has a non-variable argument `a j`, and a given point may equal `a k` for another `k`. The form with `schwarzChristoffelVertex_congr` is not canonical.

Proposed change:

Drop `@[simp]` here and let callers keep passing the hypothesis explicitly, as they all do. If bare-`simp` use is wanted, keep the attribute but state the intended use in the docstring (the hypothesis must be a local hypothesis or in the simp set), and add a separate unconditional or `Tendsto`-based lemma for the cases that really need simp.

Benefit: The simp set no longer contains a conditional rule that rarely fires. Readers do not expect an automatic `boundary → vertex` normal form that does not occur. The repository's explicit-hypothesis rewrites are unaffected, so no downstream proof changes.

Source evidence:

- `(use site)` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Corner/Basic.lean`: simpa [schwarzChristoffelBoundary_apply_prevertex a e z₀ j he] using
- `(use site)` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Polygon/Nondegenerate.lean`: rw [← schwarzChristoffelBoundary_apply_prevertex a e z₀ 0 (hfinite 0)]
- `TauCeti.schwarzChristoffelVertex_congr` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Vertex.lean`: simp only [schwarzChristoffelVertex, h]

### simp-interface: [TauCeti/ModelTheory/Scott/RigidGraph.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L44-L53)

Declaration: `TauCeti.rigidSixGraph_adj`

The lemma carries a global @[simp] attribute in a public section, so it is exported to every importing file. Its right-hand side is a 12-way disjunction of conjunctions of equalities. For any `rigidSixGraph.Adj a b` with non-literal `a` or `b`, simp would replace the compact predicate with that disjunction. It would do this wherever the graph appears, for example in goals produced by `SimpleGraph.sameAtomicType_iff`. A bare `rigidSixGraph.Adj` has no canonical reduced form, and this expansion is not one. It is an unwanted blow-up, and it hides the graph structure that later lemmas about symmetry or neighbours would want to see. In this file the attribute is never used by simp. The theorem is used only as an explicit term, `decidable_of_iff _ (rigidSixGraph_adj i j).symm`, and the other simp calls here are `simp only [...]` or `simp [rigidSixGraph]`. The attribute therefore has no benefit here and a clear downstream cost.

Proposed change:

Remove `@[simp]` from `rigidSixGraph_adj`, so it stays an explicit unfolding lemma. Callers can then opt in with `simp [rigidSixGraph_adj]` or `rw [rigidSixGraph_adj]`. If simp should decide concrete cases such as `rigidSixGraph.Adj 0 3`, add narrow lemmas for the concrete edges, or rely on the `DecidableRel` instance with `decide`. Alternatively, make the attribute local to the proof sites that need it.

Benefit: Importers no longer have `rigidSixGraph.Adj i j` silently rewritten into a 12-disjunct formula. Simp-normal forms stay compact, and the lemma remains available where explicit case analysis is wanted.

Source evidence:

- `TauCeti.instDecidableRelAdjRigidSixGraph (private local instance)` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/Scott/RigidGraph.lean`: decidable_of_iff _ (rigidSixGraph_adj i j).symm
- `TauCeti.bfEquiv_one_rigidSixGraph` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/Scott/RigidGraph.lean`: simp only [SimpleGraph.sameAtomicType_iff]

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

### simp-interface: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L74-L91)

Declaration: `sectorCurve_zero / sectorCurve_three / sectorCurve_one (knot-value lemmas)`

The closed-form values of the piecewise-defined `sectorCurve` at the knots 0, 1 and 3 are stated as plain theorems with no `@[simp]` attribute. The definition is an `if` chain, so plain `simp` cannot evaluate `sectorCurve r α 0`, `sectorCurve r α 1` or `sectorCurve r α 3` without unfolding. Downstream proofs therefore have to name the lemmas by hand in `simp only [...]` or `rw [...]`, as the sites in SectorCurveLemma.lean show. Each statement is a literal-argument evaluation with a canonical right-hand side (`0` or `↑r`), so there is no looping or ambiguity risk. The neighbouring `sectorCurve_two` has a non-normal RHS and should stay non-simp.

Proposed change:

Add `@[simp]` to `sectorCurve_zero`, `sectorCurve_three` and `sectorCurve_one`. Then downstream uses can drop the explicit lemma names, for example `simp only [F, sectorCurve_zero, sectorCurve_three, ...]` in SectorCurveLemma.lean line 141 and the `rw [..., sectorCurve_zero, sectorCurve_three, sub_self]` at line 264. `sectorCurve_closed` and `sectorCurve_passes_through_origin` would then follow by `simp`. Leave the `if`-unfolding definition itself non-simp. Keep `sectorCurve_two`, the segment lemmas and the norm lemmas as ordinary lemmas, because they have side conditions or non-canonical right-hand sides.

Benefit: Endpoint evaluations such as `F 3 - F 0` become automatic under `simp`. Users no longer need `simp [sectorCurve]`, which exposes the `if` chain and can pull in unwanted case splits.

Source evidence:

- `private theorem in SectorCurveLemma.lean (the `change F 3 - F 0 = 0` step)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: simp only [F, sectorCurve_zero, sectorCurve_three, zero_pow (by omega : n ≠ 0),
- `private theorem in SectorCurveLemma.lean (the endpoint-evaluation step after integral_eq_of_hasDerivAt_off_countable_of_le)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: sectorCurve_zero, sectorCurve_three, sub_self]
- `sectorCurve_closed` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: sectorCurve r α 0 = sectorCurve r α 3 := by rw [sectorCurve_zero, sectorCurve_three]

### simp-interface: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L131-L132)

Declaration: `CKN.Foundation.Parabolic.Morrey.positiveShell`

positiveShell is a plain def that only specializes parabolicRieszShell to a natural-number index. It has no rewrite lemma, so simp can neither expose its definition nor fold it back. Call sites therefore pass the constant itself to simp, as in `simpa [a, s, positiveShell] using hw.1` and `simpa [s, b, positiveShell] using positive_shell_cylinder_subset hR n z`. The helper `positive_shell_cylinder_subset` is stated for `parabolicRieszShell R (k : ℤ) z`, not for `positiveShell`. The goal and hypothesis therefore only match after simp unfolds the definition. `exists_positive_shell` has the same mismatch: it gives a `parabolicRieszShell` membership, and `positive_shell_cover` re-wraps it by defeq. In the other direction, simp can unfold `positiveShell` to `parabolicRieszShell R ↑n z`, but only when it is told to. Nothing gives a canonical form for `w ∈ positiveShell R n z`.

Proposed change:

Add a membership lemma such as `@[simp] theorem mem_positiveShell : w ∈ positiveShell R n z ↔ (2:ℝ)^(n:ℝ) * R ≤ parabolicRho₂ z w ∧ parabolicRho₂ z w < (2:ℝ)^((n:ℝ)+1) * R := Iff.rfl`. Alternatively, add `positiveShell_def : positiveShell R n z = parabolicRieszShell R (n:ℤ) z := rfl`. Use `positiveShell` directly in the statements of `positive_shell_cylinder_subset` and `exists_positive_shell`, so the `simpa [..., positiveShell]` unfoldings at lines 215 and 233 can become plain `hw.1` and `exact`. If the wrapper is purely an alias, a `@[reducible]` abbrev would achieve the same effect. The `Int.cast`/`Nat.cast` forms still need a simp lemma such as `Int.cast_natCast`, which simp already has.

Benefit: Readers and later files get a single canonical, loop-free normal form for shell membership. Unfolding this definition no longer needs ad hoc simp sets, and simpa calls no longer depend on definitional unfolding to match the lemma statements.

Source evidence:

- `positive_shell_integral_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: simpa [a, s, positiveShell] using hw.1
- `positive_shell_integral_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: simpa [s, b, positiveShell] using positive_shell_cylinder_subset hR n z
- `parabolicRieszShell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`: {w | (2 : ℝ) ^ (k : ℝ) * R ≤ parabolicRho₂ z w ∧

### simp-interface: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L97-L118)

Declaration: `RS.taylorCoeffAt_const_mul / RS.taylorCoeffAt_neg (unconditional linearity lemmas not tagged simp, while taylorCoeffAt_const is)`

The simp set handles `taylorCoeffAt (fun _ => c) z₀ j` (simp) and the monomial case (simp), but not the unconditional scalar-multiple and negation rules. A goal like `taylorCoeffAt (fun z => c * (z - z₀)^d) z₀ j` therefore does not simplify to `c * if j = d then 1 else 0`, because the `const_mul` step is left to a manual `rw`. The proof of `exists_taylor_remainder` does this by hand (`rw [taylorCoeffAt_const_mul, taylorCoeffAt_monomial]`), and LaurentCoeff.lean line 293 does `rw [taylorCoeffAt_const_mul]`. Both lemmas need no hypotheses, have a smaller right-hand side (a head multiplication or negation moved outside), and cannot loop. They are canonical simp lemmas, unlike the add/sub lemmas, which need analyticity hypotheses.

Proposed change:

Mark `taylorCoeffAt_const_mul` and `taylorCoeffAt_neg` as `@[simp]`. Then `simp` normalises `c * (monomial)` automatically. The manual `rw [taylorCoeffAt_const_mul, taylorCoeffAt_monomial]` in `hterm` could become `simp`, and the `split_ifs <;> simp` there would be simplified or removed. Keep in mind that `taylorCoeffAt_neg` and the simp-normal form `-g z` versus `(-1) * g z` need to be checked against existing simp lemmas such as `neg_mul` and `one_mul`.

Benefit: Callers get a canonical normal form for scalar multiples and negations of Taylor coefficients without finding the lemma names. Proofs about monomial combinations no longer need explicit rewrite chains.

Source evidence:

- `laurent coefficient proof using taylorCoeffAt_const_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/LaurentCoeff.lean`: · rw [taylorCoeffAt_const_mul]
- `RS.AnalyticAt.exists_taylor_remainder (hterm)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: rw [taylorCoeffAt_const_mul, taylorCoeffAt_monomial]

### simp-interface: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L89-L95)

Declaration: `RS.dslope_const (and RS.dslope_const_mul) – helper lemmas with no simp attribute, used only through manual rewrites`

`dslope_same` is simp in Mathlib, but `dslope` of a constant function is not. Hence `dslope (fun _ => c) z₀` stays unsimplified, and the file has to `rw [dslope_const]` by hand in `taylorCoeffAt_const`. This is an unconditional lemma with a strictly simpler right-hand side. It is also the key step for the `taylorCoeffAt_succ` unfolding that the file keeps non-simp. The lemma is public in namespace `RS` with a Mathlib-style name (`RS.dslope_const`), so it is not a clearly scoped local helper.

Proposed change:

Tag `dslope_const` with `@[simp]`. Then `simp [taylorCoeffAt_succ]` on a constant-function goal reduces fully. Also tag `taylorCoeffAt_zero_fun` (or drop it, since `taylorCoeffAt_const` with `c = 0` plus `ite_self` already gives it).

Benefit: `simp [taylorCoeffAt_succ]` on constant functions then closes goals that currently need explicit `rw`. The redundancy between `taylorCoeffAt_zero_fun` and the simp lemma `taylorCoeffAt_const` is also removed.

Source evidence:

- `dslope_same` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/DSlope.lean`: theorem dslope_same (f : 𝕜 → E) (a : 𝕜) : dslope f a a = deriv f a
- `RS.taylorCoeffAt_const` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: | succ j => rw [taylorCoeffAt_succ, dslope_const, taylorCoeffAt_zero_fun]; simp

### simp-interface: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L168-L184)

Declaration: `weakPathRepresentative (missing evaluation simp lemmas; used in weakPathRepresentative_memL2On / _l2NormSq / _pairing_eq_inner / _isPeriodic)`

`weakPathRepresentative` is defined by `if ht : t ∈ Icc 0 1 then ... else 0`, but there are no lemmas giving its normal forms: one for `t ∈ Icc 0 1` (equal to `scalarTorusRepresentative (u ⟨t, ht⟩)`) and one for `t ∉ Icc 0 1` (equal to 0). The same fact is therefore re-proved by unfolding the definition with ad hoc `simp [weakPathRepresentative, ht]`. This appears as `hfun` in `weakPathRepresentative_memL2On` and `weakPathRepresentative_l2NormSq`, as `hrep` in `weakPathRepresentative_pairing_eq_inner`, and twice in `weakPathRepresentative_isPeriodic`. It appears again in ScalarRepresentative.lean. Each use exposes the `dite` implementation. The restricted case also needs a manual `funext`, `rw` and `exact` sequence, so `simp` cannot use the fact directly.

Proposed change:

Add two lemmas right after the definition, using the statements the proofs already establish:
`@[simp] theorem weakPathRepresentative_of_mem (u) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : weakPathRepresentative u t = scalarTorusRepresentative (u ⟨t, ht⟩)`, proved by `funext x; simp [weakPathRepresentative, ht]`.
`@[simp] theorem weakPathRepresentative_of_not_mem (u) {t : ℝ} (ht : t ∉ Icc (0:ℝ) 1) : weakPathRepresentative u t = fun _ => 0`.
Also add a version for `t : Icc (0:ℝ) 1`, where the coerced time is `(t : ℝ)`. Its statement should be `weakPathRepresentative u t = scalarTorusRepresentative (u t)`, proved with `t.property` and `Subtype.coe_eta`. Then replace the `hfun` blocks by `simp [weakPathRepresentative_of_mem u t.property]` or `rw`. The four-way `simp [weakPathRepresentative, ht]` calls in the downstream file can use the same lemmas. The conditional lemmas have side conditions that the hypothesis `ht` discharges, and the right-hand side contains no `weakPathRepresentative`, so no cycle can arise.

Benefit: The normal form of the definition is stated once. Proofs and downstream code can rewrite without unfolding the `dite`. About five copies of the `funext; simp [weakPathRepresentative, ...]` pattern shrink to one-line uses. If the representative's definition changes, only the evaluation lemmas need updating.

Source evidence:

- `weakPathRepresentative` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: fun t x => if ht : t ∈ Icc (0 : ℝ) 1 then
    scalarTorusRepresentative (u ⟨t, ht⟩) x else 0
- `synchronizedScalarRepresentative_testPairing (case with a good time)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/ScalarRepresentative.lean`:             rw [hpath]
            simp [weakPathRepresentative, ht]

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

### fragile-proofs: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L410-L415)

Declaration: `tendsto_log_mul_self_nhdsLT_zero`

The proof rewrites the third occurrence of `0` in the goal by position. The goal is `Tendsto (-(f) ∘ |·|) (𝓝[<] 0) (𝓝 0)`, and `𝓝[<] 0` unfolds to `Iio 0` and the point `0`. So the index 3 silently depends on how many hidden zeros the `𝓝[<]` notation carries and on their traversal order. A change to the `nhdsWithin` notation or to how `tendsto_nhdsWithin_congr` states its goal would make it rewrite the wrong `0`, or fail. The following `push _ ∈ _ at hx` and the `simp only [...]` close are also a sensitive chain for what is really `hx.ne`.

Proposed change:

Avoid rewriting a goal by occurrence index. State the target limit explicitly, e.g. `have := (h.comp (tendsto_abs_nhdsNE_zero.mono_left ?_)).neg` and then `simpa using this`. Alternatively use `neg_zero ▸ ...`, or `convert` against `(𝓝 (-0))` with `neg_zero`. The side goal `𝓝[<] 0 ≤ 𝓝[≠] 0` can be closed with `nhdsWithin_mono _ fun x (hx : x < 0) => hx.ne` or `nhdsLT_le_nhdsNE`, so the `push` and `simp only` steps are not needed.

Benefit: The proof stops depending on the count and ordering of `0` occurrences. It then survives routine changes to notation or lemma statements, and the intended limit `-0 = 0` is visible to the reader.

Source evidence:

- `tendsto_log_mul_self_nhdsLT_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: refine (h.comp (tendsto_abs_nhdsNE_zero.mono_left ?_)).neg

### fragile-proofs: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L53-L76)

Declaration: `tendsto_rpow_atTop_of_base_lt_one`

The proof refers to `rcases lt_trichotomy` branches by the auto-generated constructor-path names `inl`, `inr.inl` and `inr.inr`. After `rfl` is substituted, these names depend on the Or structure of `lt_trichotomy`. They also conflict with the explicit `?exp`/`?cos` names used elsewhere in the same proof. The first branch also relies on the exact shape of `Real.rpow_def_of_nonpos`: `simp_rw [..., hb.ne, ite_false]` expects an `if b = 0 then .. else ..` form, and `rw [..., (one_mul (1 : ℝ)).symm]` must find the right `1`. If the definitional lemma is restated, or `lt_trichotomy` is reordered, these steps break.

Proposed change:

Use structured `rcases ... with hb | rfl | hb` followed by bullets `·`, or name the cases via `obtain`. Replace `simp_rw [..., hb.ne, ite_false]` with `rw [Real.rpow_def_of_nonpos hb.le]` and `simp only [hb.ne, if_false]`, or supply the function equality with a `Tendsto.congr` and an explicit `show`. For the `1 * 1` rewrite, give an explicit `have : (fun x => ...) =o[atTop] fun _ => (1:ℝ)` via `IsLittleO.mul_isBigO` and `by simpa using`.

Benefit: The branch structure no longer depends on generated names, and the `1 * 1` rewrite no longer depends on where a `1` happens to occur. This makes the proof less brittle to changes in `lt_trichotomy` or the `rpow_def` lemmas.

Source evidence:

- `tendsto_rpow_atTop_of_base_lt_one` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: rw [← isLittleO_const_iff (c := (1 : ℝ)) one_ne_zero, (one_mul (1 : ℝ)).symm]

### fragile-proofs: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L73-L75)

Declaration: `Algebra.TensorProduct.basis_repr_symm_apply`

The proof unfolds both `basis` and `basisAux`. It then depends on simp normalising the `Equiv.uniqueProd` / `finsuppTensorFinsupp` / `TensorProduct.congr` / `Finsupp.lcongr` chain, using the explicit lemma `Equiv.uniqueProd_symm_apply`. The public lemma `basis_repr_tmul`, proved just above, already gives the forward behaviour of `(basis A b).repr`. Any routine change to how `basisAux` is assembled (for example a different equivalence for the `PUnit` factor or a reordered composition) would break this proof. It would also break if simp-normal forms of the symm of those equivalences changed.

Proposed change:

Prove it through the public interface, without unfolding `basis` or `basisAux`. Rewrite with `LinearEquiv.symm_apply_eq`, so the goal becomes `Finsupp.single i a = (basis A b).repr (a ⊗ₜ b.repr.symm (Finsupp.single i 1))`. Then use `basis_repr_tmul`, `Basis.repr_symm_single` (or `LinearEquiv.apply_symm_apply`) and `Finsupp.mapRange_single`/`Finsupp.smul_single`, so the proof only needs `map_one` and `smul_eq_mul`. The proof then depends only on the stated characterisation of `basis_repr_tmul`.

Benefit: The proof no longer depends on the internal construction of `basisAux` or on `Equiv.uniqueProd_symm_apply`. The definition can be refactored without breaking it, and the argument (a basis vector maps to `single i 1`) is visible to the reader.

Source evidence:

- `Algebra.TensorProduct.basis_repr_tmul` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: (basis A b).repr (a ⊗ₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.repr m)
- `Algebra.TensorProduct.basisAux` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: (finsuppTensorFinsupp R R A R PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid R A))

### fragile-proofs: [Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean#L101-L103)

Declaration: `CategoryTheory.Functor.IsWellOrderContinuous.restriction_setIci`

The proof gets `¬ IsMin m` from `hm` by the positional projection `.1` of the structure `Order.IsSuccLimit`. That ties the proof to the field order. Reordering the fields, or adding one, silently changes what `.1` means and breaks this step, with a confusing error. The structure has a named field `not_isMin`, and `Order.IsSuccLimit.not_isMin` is the public accessor.

Proposed change:

Replace `apply hm.1` by `apply hm.not_isMin`, and keep the following `rintro ⟨k, hk⟩ hkm; exact h'.trans hk`. The same change applies to `hm.1` in Set.Ici.isSuccLimit_coe, but that is in another file.

Benefit: The proof depends on the named field instead of its position. A reader can see that the step uses non-minimality of the limit element.

Source evidence:

- `Order.IsSuccLimit` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Limit.lean`: protected not_isMin : ¬ IsMin a
- `Order.not_isSuccLimit_of_isSuccArchimedean` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Limit.lean`: fun h ↦ h.not_isMin h.isSuccPrelimit.isMin

### fragile-proofs: [Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean#L90-L96)

Declaration: `CategoryTheory.Functor.IsWellOrderContinuous.restriction_setIci`

The finality proof works through a local `let` function defined by pattern matching on nested subtypes. The following steps then depend on how this term unfolds: `dsimp only [f]`, the `push _ ∈ _ at hj'` rewrite, and the closing `by rfl` on the unreduced `f` application. If the elaborated form of the `fun ⟨⟨a, ha⟩, ha'⟩` match changes, or the `Monotone.final_functor_iff` goal is stated differently, these steps break without any change to the maths. Defining `f` by projections, `fun x ↦ ⟨x.1.1, x.2⟩`, would remove the match compilation. Alternatively, the goal could be stated with explicit membership lemmas such as `Set.mem_Iio`.

Proposed change:

Define `f` with projections, `fun x ↦ ⟨x.1.1, x.2⟩`, so there is no match to unfold. Replace `push _ ∈ _ at hj'` with the explicit `Set.mem_Iio` (e.g. `simp only [Set.mem_Iio] at hj'`). Give the witness in the last bullet as a term whose `≤` proof is by `le_rfl`, rather than relying on `rfl` to see through `f`.

Benefit: The proof depends less on how the local `let f` unfolds, so a routine change to simp normal forms or match compilation is less likely to break it. The finality argument also becomes easier to read.

Source evidence:

- `CategoryTheory.Functor.IsWellOrderContinuous.restriction_setIci` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean`: · exact ⟨⟨⟨j', h.le⟩, hj'⟩, by rfl⟩

### fragile-proofs: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L768-L772)

Declaration: `VectorBundleCore.localTriv_continuousLinearMapAt`

The proof uses non-terminal `simp_all` followed by a bare `rfl`. `simp_all` simplifies every hypothesis and the goal with the full simp set (including the `mfld_simps`/`@[simp]` lemmas of this file such as `localTriv_apply`, `coordChange_self`, `coe_coordChange`), and the `rfl` depends on whatever normal form it leaves. Adding a simp lemma or changing a simp-normal form could leave a different goal, or close it so that `rfl` errors with 'no goals'. The mathematical content is just `continuousLinearMapAt_apply_of_mem` plus `localTriv_apply`, and this is hidden.

Proposed change:

Rewrite with the public lemma instead of relying on `simp_all`: after `ext1 v`, use `rw [Trivialization.continuousLinearMapAt_apply_of_mem R (Z.localTriv i) hb v]` (or `(Z.localTriv i).continuousLinearMapAt_apply_of_mem R hb v`) and close with `rfl`, which holds by `localTriv_apply`. Alternatively use `simp only [Trivialization.continuousLinearMapAt_apply_of_mem _ hb, localTriv_apply]`.

Benefit: The proof states which lemmas are used, and it no longer depends on the global simp set or on `simp_all` handling unrelated hypotheses. It is less likely to break when simp lemmas change.

Source evidence:

- `Bundle.Trivialization.continuousLinearMapAt_apply_of_mem` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: (continuousLinearMapAt R e b) y = (e ⟨b, y⟩).2
- `VectorBundleCore.localTriv_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩

### fragile-proofs: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L939-L944)

Declaration: `VectorPrebundle.toVectorBundle`

The proof gets the `IsLinear` instances needed by `Trivialization.coordChangeL_apply` by `have`-ing the linearity lemma and then `rw [trivializationOfMemPretrivializationAtlas] at h₁ h₂`, which unfolds the wrapper definition so that the local hypotheses syntactically match the `a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas` term in the goal. The proof therefore depends on the definitional body of `trivializationOfMemPretrivializationAtlas` and on the instance-synthesis behaviour under the `backward.isDefEq.respectTransparency false` option. If the definition is reshaped, the `rw` fails or the instances stop being found. The final `exacts [rfl, hb]` also depends on the order and form of the side goals produced by the `rw`.

Proposed change:

State `linear_trivializationOfMemPretrivializationAtlas` (or an instance version of it) directly for the term that appears in the goal, `a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he`. Alternatively, supply the instances explicitly to `Trivialization.coordChangeL_apply` instead of rewriting hypotheses. Then provide the membership side condition `hb` as an explicit argument, e.g. `Trivialization.coordChangeL_apply _ _ hb v`, so the closing step is not `exacts [rfl, hb]`.

Benefit: The proof no longer depends on unfolding a definition or on the order of generated side goals. It states which trivialization carries which linear structure, which matches the public API.

Source evidence:

- `VectorPrebundle.linear_trivializationOfMemPretrivializationAtlas` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: Trivialization.IsLinear R (trivializationOfMemPretrivializationAtlas a he)
- `VectorPrebundle.trivializationOfMemPretrivializationAtlas` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: a.toFiberPrebundle.trivializationOfMemPretrivializationAtlas he
- `Bundle.Trivialization.coordChangeL_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: coordChangeL R e e' b y = (e' ⟨b, e.symm b y⟩).2

### fragile-proofs: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L456-L456)

Declaration: `Bundle.Trivialization.continuousLinearEquivAt`

`convert` followed by `ext; simp [hb]` depends on the exact goals `convert` generates. These are the shape of the `invFun` goal inside the structure update, how `ext` splits it, and which simp lemmas fire. The needed fact is just that `e.symm b` and `⇑(e.symmL R b)` agree pointwise on `b ∈ e.baseSet`, which is `symmL_apply`. A routine change to the `toFun`/`invFun` fields or to the `ext` lemmas would change what `convert` leaves.

Proposed change:

Use the public lemma explicitly: `continuous_invFun := (e.symmL R b).continuous.congr fun y => e.symmL_apply hb y`. This is the same `Continuous.congr` pattern already used in the `symmL` definition, which uses `continuous_zero.congr fun x => ...`.

Benefit: This is a term-mode proof that names the lemma it relies on (`symmL_apply`). It does not depend on what `convert` and `ext` produce, so it is more robust and easier to read.

Source evidence:

- `Bundle.Trivialization.symmL_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: e.symmL R b y = e.symm b y
- `Bundle.Trivialization.symmL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: exact continuous_zero.congr fun x => (e.symmₗ_apply_of_notMem hb x).symm }

### fragile-proofs: [Mathlib/Control/Traversable/Equiv.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Control/Traversable/Equiv.lean#L78-L83)

Declaration: `Equiv.lawfulFunctor'`

The proof destructs the instance with `cases F`, unfolds `Equiv.functor`, then runs `congr`. The `<;> [t₁; t₂]` combinator needs exactly two goals, in the order `map`, then `mapConst`. That order and count come from `congr`'s output and from the field layout of `Functor`. The trailing `rfl` closes whatever `rw` leaves, so it hides what is actually being proved. If `congr` closes or reorders a goal, or `Functor` gets another field, the proof breaks, and the failure is a tactic-shape error that doesn't mention the real cause.

Proposed change:

State the equality of instances through the fields directly. For example, prove `F = Equiv.functor eqv` with `Functor.ext`, if available, or `cases F` followed by `congr 1` with `funext`/`ext` and `exact`, using `h₀` and `h₁` as explicit terms. Alternatively, skip the instance equality. Build `LawfulFunctor` for `t'` using `h₀` and `h₁` to rewrite `map` and `mapConst` in the laws: `id_map := fun x => by rw [h₀]; exact Equiv.id_map eqv x`. Each field is then handled separately and doesn't depend on goal order.

Benefit: Each field is proved by a named step using `h₀`/`h₁` explicitly. A change to the `Functor` structure or to `congr`'s goal ordering would then not silently break the proof.

Source evidence:

- `Equiv.lawfulFunctor'` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Control/Traversable/Equiv.lean`: congr <;> ext <;> [rw [← h₀]; rw [← h₁]] <;> rfl

### fragile-proofs: [Mathlib/Control/Traversable/Equiv.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Control/Traversable/Equiv.lean#L169-L171)

Declaration: `Equiv.isLawfulTraversable'`

The `comp_traverse` field uses a chain of unguided `rw [h₂ ...]` calls, then `congr`, then another `rw [h₂]`. Each `h₂` rewrite has the pattern `traverse ?f` with implicit applicative arguments. Which occurrence gets rewritten depends on traversal order and on instance unification. `congr` on an `Comp.mk (_ <$> _)` goal depends on how deep it decomposes. Changing the `Comp` definition, the form of `comp_traverse`, or the `congr` depth would break this step, and the cause would be hard to see. The `naturality` field has the same repeated `rw [h₂, ..., h₂]`.

Proposed change:

Make the rewrites explicit and prove the shape directly. For example, first `have := h₂ ...` at the specific applicative and function, using `Comp.instApplicativeComp` where needed. Then `rw [h₂ (F := Comp G F) (Comp.mk ∘ Functor.map _ ∘ _), Equiv.comp_traverse]` and finish with `simp only [h₂]` or `congr 1`. Prove the fields as `Equiv.comp_traverse`-based calc steps, so it is clear which `traverse` is rewritten at which applicative.

Benefit: Naming the applicative and function for each `h₂` instantiation removes the dependence on rewrite order and on how far `congr` descends. The proof then states which occurrences of `traverse` are being replaced.

Source evidence:

- `Equiv.isLawfulTraversable'` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Control/Traversable/Equiv.lean`: naturality _ _ _ _ _ := by rw [h₂, Equiv.naturality, h₂]

### fragile-proofs: [Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L123-L127)

Declaration: `CliffordAlgebra.contractLeft_ι_mul (also contractLeft_ι, contractLeft_algebraMap)`

The proofs rely on Lean unifying `contractLeft d (ι Q a * b)` with `foldr' Q ?f ?hf ?n (ι Q ?m * ?x)`. That means unfolding the `contractLeft` structure literal and its coercion chain, and the proof only works because the definition is compiled with `backward.defeqAttrib.useBackward true` (line 76), and `contractLeftAux` with `backward.isDefEq.respectTransparency false` (line 59, commented only 'needed below'). The `?hf` argument has to be supplied by hand because elaboration can no longer infer it (see the 'Porting note'). The same pattern is copied in `contractLeft_ι` and `contractLeft_algebraMap`. A routine change to transparency or defeq behaviour, or to how `foldr'` is defined, would break all three lemmas and the options would have to be kept alive.

Proposed change:

State the unfolding once as an explicit lemma, e.g. `theorem contractLeft_apply (d) : contractLeft (Q := Q) d = foldr' Q (contractLeftAux Q d) (contractLeftAux_contractLeftAux Q d) 0 := rfl`, and have the three lemmas use `rw [contractLeft_apply, foldr'_ι_mul]`, `rw [contractLeft_apply, foldr'_ι]` and so on. The `hf` argument then appears explicitly. Only one place (the `rfl`) depends on the defeq of the structure literal, and the backward-compat options are needed only there.

Benefit: The defeq dependency is isolated in one `rfl` and documented by a lemma name. The three downstream proofs use only the public `foldr'_*` API with an explicit argument, so they stay valid if elaboration or transparency changes, and the 'Porting note' hack disappears.

Source evidence:

- `CliffordAlgebra.foldr'_ι_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Fold.lean`: foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x)
- `CliffordAlgebra.contractLeft` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: set_option backward.defeqAttrib.useBackward true in

### fragile-proofs: [Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L279-L281)

Declaration: `CliffordAlgebra.changeForm_ι_mul`

The proof applies `foldr_mul` by unifying with `changeForm h (ι Q m * x)`, which unfolds `changeForm` implicitly. It then closes the goal with a bare `rfl` that has to unfold `changeFormAux` (a `@[simps!]` linear-map subtraction), the coercions of `LinearMap.sub` and `∘ₗ`, and the `ι Q' m * _ - contractLeft (B m) _` form. The `rfl` depends on the exact shape of `changeFormAux` and the instance unfolding. Changing the definition's internals, for example how `v_mul` is built or the order of the subtraction, would break it with no clear error. The simp lemma `changeFormAux_apply_apply` already exists for this step.

Proposed change:

Replace the final `rfl` with the generated lemma, for example `by rw [foldr_ι, changeFormAux_apply_apply]`, or use `show`/`unfold changeForm` followed by `rw [foldr_mul, foldr_ι, changeFormAux_apply_apply]`. This states the intended unfolding explicitly.

Benefit: The step is checked through the public simp lemma instead of definitional unfolding, so it survives refactors of `changeFormAux`. A reader can also see which identity is being used.

Source evidence:

- `CliffordAlgebra.changeFormAux` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: v_mul - contractLeft ∘ₗ B
- `CliffordAlgebra.changeFormAux_changeFormAux` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: simp only [changeFormAux_apply_apply]

### fragile-proofs: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L53-L58)

Declaration: `ZMod.toCircle_intCast`

The proof is a long `rw` chain that unfolds `AddCircle.toCircle` and `toCircle_addChar` and then uses `Function.Periodic.lift_coe` and `AddChar.coe_mk`. It depends on `AddCircle.toCircle` being defined as `Function.Periodic.lift ...` and on the structure-literal form of `toCircle_addChar`. Changing how `AddCircle.toCircle` is defined, or turning `toCircle_addChar` into a coercion of another bundled map, would break it. `AddCircle.toCircle_apply_mk` already states the value on a coset and is the public interface for this. The closing `ring_nf` also depends on the normal form it produces.

Proposed change:

Rewrite with the public API: `rw [toCircle, AddChar.compAddMonoidHom_apply, toAddCircle_intCast]`. Then close the goal using `AddCircle.toCircle_apply_mk` (the `toCircle_addChar` unfolding is still needed) and `Circle.coe_exp`. Finish with an explicit `congr 1; push_cast; ring` or `by rw [show ... = ... by ring]` instead of `ring_nf`. This avoids `Function.Periodic.lift_coe`, `AddCircle.toCircle` unfolding and the order dependence of the chain.

Benefit: The proof then relies on the stated lemma `toCircle_apply_mk` and not on how `AddCircle.toCircle` is implemented. Redefining that map, or changing the normal form of `ring_nf`, would no longer break it.

Source evidence:

- `AddCircle.toCircle_apply_mk` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`: theorem toCircle_apply_mk (x : ℝ) : @toCircle T x = Circle.exp (2 * π / T * x) :=
- `AddCircle.toCircle` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean`: (@scaled_exp_map_periodic T).lift

### fragile-proofs: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L139-L143)

Declaration: `rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val`

The proof runs `simp` with a reversed lemma (`← ZMod.toCircle_natCast`), removes a default simp lemma (`-ZMod.natCast_val`) and adds `natCast_zmod_val`. These flags exist only to stop `simp` looping or rewriting `((j.val : ℕ) : ZMod n)` to `j.cast`. The proof therefore depends on the current default simp set and on how `simp` orders these rewrites. Adding or removing a simp lemma on `ZMod.val` or casts could break it. The needed fact is exactly `ZMod.toCircle_apply` after the two projection lemmas.

Proposed change:

Use a short explicit rewrite: `rw [rootsOfUnityCircleEquiv_apply, ZMod.rootsOfUnityAddChar_val, ZMod.toCircle_apply]`. This may need a `push_cast` or `simp only` for coercion bookkeeping; I have not checked this. The `-ZMod.natCast_val` and `← toCircle_natCast` tricks are then not needed.

Benefit: The proof states the mathematical steps: unfold the equivalence, then the character, then apply the explicit formula. It no longer depends on `simp` set membership or on reversed-rewrite behaviour.

Source evidence:

- `ZMod.toCircle_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: toCircle j = exp (2 * π * I * j.val / N)
- `rootsOfUnityCircleEquiv_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: ((rootsOfUnityCircleEquiv n w).val : ℂ) = ((w.val : Circle) : ℂ)

### fragile-proofs: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L150-L152)

Declaration: `bijective_rootsOfUnityAddChar`

Injectivity is proved by `simp` unfolding the definition `ZMod.rootsOfUnityAddChar`, so it depends on the internal construction `⟨toUnits (ZMod.toCircle x), _⟩` and on the simp normal form of the resulting equation between subtype/unit values. Changing how the character is built, for example via `restrictRootsOfUnity`, would break this proof even though the public lemma `rootsOfUnityAddChar_val` would still hold.

Proposed change:

Prove injectivity from the existing interface lemma `rootsOfUnityAddChar_val`. Take `h : rootsOfUnityAddChar n a = rootsOfUnityAddChar n b`, apply `ZMod.injective_toCircle`, and use `congrArg Subtype.val h` together with `rootsOfUnityAddChar_val` (possibly needing `Units.ext_iff`). Do not unfold `rootsOfUnityAddChar` in the simp set.

Benefit: The proof then relies on the stated characterization lemma, not on the definition's body, so redefining `rootsOfUnityAddChar` while keeping `rootsOfUnityAddChar_val` leaves it intact.

Source evidence:

- `ZMod.rootsOfUnityAddChar_val` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: (rootsOfUnityAddChar n x).val = toCircle x
- `ZMod.rootsOfUnityAddChar` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: toFun x := ⟨toUnits (ZMod.toCircle x), by ext; simp [← AddChar.map_nsmul_eq_pow]⟩

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

### fragile-proofs: [TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L50-L52)

Declaration: `Matrix.mem_range_scalar_of_commute_specialOrthogonalGroup (hoff: hli, hlj)`

`simp_all` runs over the entire local context. That context holds the anonymous membership hypothesis, `hl`, `hcard`, `hij`, `hn`, `h2` and the universally quantified `hM`. Each of these is simplified and used to rewrite the others. The proof only needs `hl : l ∉ {i, j}`. Whether it succeeds depends on how the unrelated hypotheses simplify, so adding a hypothesis or changing a simp lemma could make it loop, fail, or close the goal by a different route. The proof also relies on the structure of the name `hl` coming out of the `obtain`.

Proposed change:

State the dependency explicitly, for example `have hli : l ≠ i := fun h ↦ hl (by simp [h])` and `have hlj : l ≠ j := fun h ↦ hl (by simp [h])`. Alternatively use `simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl` once, then `exact ⟨hli, hlj⟩ := hl`, which gives both inequalities from `hl` alone.

Benefit: The proof depends only on `hl` and the `Finset.mem_insert`/`Finset.mem_singleton` facts. It no longer breaks when unrelated hypotheses or simp lemmas change, and a reader can see where `l ≠ i` and `l ≠ j` come from.

Source evidence:

- `Finset.exists_mem_notMem_of_card_lt_card` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Data/Finset/Card.lean`: theorem exists_mem_notMem_of_card_lt_card (h : #s < #t) : ∃ e, e ∈ t ∧ e ∉ s

### fragile-proofs: [TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L70-L75)

Declaration: `Matrix.mem_range_scalar_of_commute_specialOrthogonalGroup (hdiag)`

The proof rewrites a non-beta-reduced `congrArg` hypothesis with two successive `rw [← mulVec_mulVec]`, which depends on the order in which the pattern matches. It then runs two `simp only` passes, with `g` being unfolded in the first, and closes with a bare `exact h`. That `exact` only works if the simp-normalised `h` is syntactically `M i i = M j j`, with the orientation and `if` branches resolved exactly as expected. A routine change to `coordinateRotation_mulVec` (for example reordering the `if` branches) or to the `mulVec_mulVec` statement would break the chain with an opaque mismatch. The same pattern appears in `hoff` (lines 61-64) with `hfix`.

Proposed change:

Make the intermediate facts explicit. For example, prove `have h1 : (g : Matrix n n R) *ᵥ (M *ᵥ Pi.single i 1) = M *ᵥ ((g : Matrix n n R) *ᵥ Pi.single i 1)` directly from `(hM g).eq` via `mulVec_mulVec`. Then evaluate the two sides at `j` using `coordinateRotation_col_left` and `coordinateRotation_mulVec`. Finish with `simpa using` or `linarith`-style closing, not `exact h` after shape-sensitive `simp only`. Alternatively, state the two evaluated entries as separate `have`s so that each rewrite is a single named step.

Benefit: Each step names the lemma it uses, and the closing step no longer relies on an exact syntactic form produced by a chain of `simp only` calls. The argument is therefore easier to read and less likely to break when the simp-normal form of the coordinate-rotation lemmas changes.

Source evidence:

- `coordinateRotation_mulVec` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/CoordinateRotation.lean`: if a = i then -w j else if a = j then w i else w a

### fragile-proofs: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L208-L211)

Declaration: `TauCeti.hasDerivAt_schwarzChristoffelBoundary (hcast step)`

The proof gets the derivative of a real-to-complex cast by going through the continuous linear map `ofRealCLM` and `scomp`. It then cleans up the resulting `ofRealCLM` application with an open-ended `simpa` using the default simp set plus `Function.comp_def`. This depends on the exact form `scomp` produces and on how the simp set normalises it. Mathlib already states this as a lemma, so the proof reaches into implementation details instead of using a public lemma. A routine change to the simp set or to the `scomp` output shape would break it.

Proposed change:

Replace the `hcast` proof with the public lemma `HasDerivAt.ofReal_comp`. Apply it to `hInt`, i.e. `hInt.ofReal_comp`, possibly wrapped in `by simpa using hInt.ofReal_comp` if the coercion form does not match syntactically. This removes the `ofRealCLM` and `Function.comp_def` machinery.

Benefit: The cast-derivative step becomes a one-line call to a documented lemma. It no longer depends on the shape of the `scomp` output or on the default simp set.

Source evidence:

- `HasDerivAt.ofReal_comp` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Analysis/Complex/RealDeriv.lean`: theorem HasDerivAt.ofReal_comp {f : ℝ → ℝ} {u : ℝ} (hf : HasDerivAt f u z) :
    HasDerivAt (fun y : ℝ => ↑(f y) : ℝ → ℂ) u z

### fragile-proofs: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L90-L90)

Declaration: `TauCeti.schwarzChristoffelBoundary_eq_of_tendsto and continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one (closure computations)`

The two closure-membership side goals (here and at line 158) are proved by `rw` with the Mathlib lemma `Complex.closure_setOfPred_lt_im`, followed by a bare `simp`. The `rw` only works because `upperHalfPlaneSet` happens to be an `abbrev`, and it fixes the exact rewrite name. That name was changed recently: the old `closure_setOf_lt_im` is now a deprecated alias. The lemma is already a `@[simp]` lemma, so spelling out the `rw` adds a dependency on the name and on the abbrev's reducibility without adding any mathematical content. The same two-step argument is duplicated in the file.

Proposed change:

Prove the fact once as a small private lemma, for example `(x : ℝ) : (x : ℂ) ∈ closure upperHalfPlaneSet`, using `simp [upperHalfPlaneSet]` or the `rw` in a single place. Use that lemma at lines 90 and 158. Line 158 would then only need to show `(x : ℂ) ∈ closure upperHalfPlaneSet` for each `x` in `s`.

Benefit: A future rename or restatement of the closure lemma, or a change to how `upperHalfPlaneSet` is defined, would then need one fix instead of two. The `extendFrom` arguments would also read more clearly.

Source evidence:

- `Complex.closure_setOfPred_lt_im` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Analysis/Complex/ReImTopology.lean`: @[deprecated (since := "2026-07-09")] alias closure_setOf_lt_im := closure_setOfPred_lt_im
- `UpperHalfPlane.upperHalfPlaneSet` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Analysis/Complex/UpperHalfPlane/Basic.lean`: abbrev upperHalfPlaneSet := {z : ℂ | 0 < z.im}

### fragile-proofs: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L88-L90)

Declaration: `TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg (and structureConstant_neg_neg_eq_neg_iff)`

The side-condition proof for `(-γ : H → K) = -α + -β` is a hand-counted sequence of three `Weight.coe_neg` rewrites followed by `hαβ`. Each `rw` rewrites only the first matching instance pattern, so the proof depends on exactly three distinct negated weights appearing in this order. Any routine change breaks it, such as making `coe_neg` a simp lemma, changing the coercion form, or changing the statement shape. The same fragile block is pasted into the statement of both theorems here (lines 88–90 and 143–145) and into the Symmetry file, so one change means several edits.

Proposed change:

State the fact once as a small named lemma, for example `coe_neg_eq_neg_add_neg (hαβ : (γ : H → K) = α + β) : ((-γ : Weight K H L) : H → K) = ((-α : Weight K H L) : H → K) + ((-β : Weight K H L) : H → K)`. Prove it with `simp only [Weight.coe_neg, hαβ]; abel`, or `by simp [hαβ]; abel` if the simp normal form allows. Use the lemma in all statements instead of the inline `by rw ...; abel` blocks. This removes the counted rewrites and the duplicated proof terms.

Benefit: The dependence on rewrite order and count is confined to one proof. Statements and callers become shorter and easier to read, and a change to the `Weight.coe_neg` API needs one fix instead of many.

Source evidence:

- `TauCeti.IsSl2System.structureConstant_neg_neg_of_hom` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Symmetry.lean`: rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]
- `TauCeti.IsSl2System.structureConstant_neg_neg_eq_neg_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean`: rw [Weight.coe_neg, Weight.coe_neg, Weight.coe_neg, hαβ]

### fragile-proofs: [TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean#L137-L150)

Declaration: `TauCeti.NumberField.FifthCyclotomic.map_span_five_eq_pow_four`

The proof reaches the general `p ^ (k+1)` lemma by hand, and several steps depend on incidental elaboration details. (1) `hK : IsCyclotomicExtension {5 ^ (0 + 1)} ℚ K` is never mentioned by name. It only works because `map_eq_span_zeta_sub_one_pow` finds it as a local instance, so a later `clear_unused`, a linter cleanup or a change to how the lemma takes `hK` would break it silently. (2) `rw [zero_add, pow_one]` is applied twice to massage `5 ^ (0 + 1)`, so the goal's exact syntactic form matters. (3) `rw [Nat.cast_ofNat] at h` assumes `h` contains exactly a `((5 : ℕ) : ℤ)` cast, in the form the lemma's `𝒑` is stated with. If Mathlib changes how `𝒑 = span {(p : ℤ)}` is written, or the numeral cast is simplified earlier, the `rw` fails with 'did not find instance'. (4) The final `rw` rewrites `𝔭` and then relies on `h`'s left-hand side matching the goal's `span {(5 : ℤ)}` syntactically.

Proposed change:

Avoid the manual `0 + 1` rewrites and follow Mathlib's own pattern in `eq_span_zeta_sub_one_of_liesOver'` and `ramificationIdx_span_zeta_sub_one'`. Convert the instance and the root-of-unity hypothesis with `rw [← pow_one 5] at hK hζ` (or `show`/`exact` using that `5 ^ (0 + 1)` is defeq to `5`), and call `IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow 5 0 hζ`. Then close the goal with `simpa using` or `Nat.cast_ofNat`-insensitive `convert`, so no `rw ... at h` is needed. For example, state `h` with an explicit type annotation `(span {(5 : ℤ)}).map (algebraMap ℤ (𝓞 K)) = span {hzeta.toInteger - 1} ^ Module.finrank ℚ K` and prove it by `simpa using ...`. That documents the intended shape and fails only at one clearly localised place. Alternatively, derive the statement from the already-proved public `ramificationIdx_eq_four` and `inertiaDeg_eq_one`, if Mathlib exposes a lemma turning `ramificationIdx` into `map p = P ^ e`.

Benefit: The proof no longer depends on an unnamed local instance, on two `rw` normalisations of `5 ^ (0 + 1)`, or on the exact cast form of `p`. Small refactors of the Mathlib lemma's statement would then not break this declaration, and a reader can see which hypothesis the general lemma needs.

Source evidence:

- `IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`: rw [← pow_one p] at hK hζ
  exact eq_span_zeta_sub_one_of_liesOver p 0 K hζ P
- `IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`: (map (algebraMap ℤ (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module.finrank ℚ K

### fragile-proofs: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L372-L377)

Declaration: `TauCeti.exists_isSolidTorusNeighborhood (injectivity step `hinj`)`

The proof passes the arguments by the binder names `a₁`/`a₂` from the unfolded definition of `Function.Injective` (`∀ ⦃a₁ a₂⦄, ...`). Those names are an implementation detail of a core definition. It then feeds `h` into a goal that only matches by defeq through `Set.domRestrict` applied to the normal-tube embedding. Next it depends on the exact output shape of `simp only [Subtype.mk.injEq, Prod.mk.injEq] at h'`, destructuring it positionally as `⟨h₂, h₁⟩`. Renaming the binders, or changing how `domRestrict` or the tube map is stated, would break the step.

Proposed change:

State the intermediate equality explicitly, for example `have h' : (⟨_, hmem q⟩ : normalTube (𝓡 1) f ε) = ⟨_, hmem q'⟩ := hemb.injective h`. Pin the type of `h` with `show` so the `domRestrict` unfolding is explicit. Extract the components with `congrArg (fun p => p.1.1) h'` and `congrArg (fun p => p.1.2) h'`, or `Subtype.ext_iff`, and avoid the positional `simp only ... at h'`. Alternatively, add a small lemma to the tube file saying the tube map is injective in terms of `(z, v) ↦ f z + v`.

Benefit: The proof no longer depends on core binder names or on the simp-normal form of the hypothesis. A reader sees directly which equality of pairs is being derived.

Source evidence:

- `Function.Injective` in `/home/kim/.elan/toolchains/leanprover--lean4---v4.36.0-rc1/src/lean/Init/Data/Function.lean`: ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
- `TauCeti.exists_isOpenEmbedding_normalTube` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Geometry/Manifold/TubularNeighborhood/Euclidean.lean`: IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2)

### fragile-proofs: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L384-L400)

Declaration: `TauCeti.exists_isSolidTorusNeighborhood (openness of the image, `convert ... using 1`)`

`convert ... using 1` discards the stated goal and keeps whatever equality of sets `convert` produces. The proof then runs `ext x` and uses `rintro` patterns such as `⟨⟨⟨z, v⟩, hzv⟩, hvr, rfl⟩`. These depend on the exact form of the image of a subtype-valued `domRestrict` map: `Set.image` membership, nested subtype and product anonymous constructors, and a `rfl` substitution that needs definitional unfolding of `domRestrict`. A routine change would break all of this. Examples are a different `convert` congruence depth, a restatement of the tube embedding, or a change to the `SolidTorus` or `Set.image` unfolding. The failure would also be far from its cause.

Proposed change:

First prove `have himg : (fun q : SolidTorus => f q.2 + r • ψ q.2 q.1) '' {p | ‖(p.1 : ℂ)‖ < 1} = (normalTube (𝓡 1) f ε).domRestrict (fun p : Circle × ℝ³ => f p.1 + p.2) '' {q | ‖(q : Circle × ℝ³).2‖ < r}`, with the exact type spelled out. Prove it by `Set.ext` and the two inclusions. Then close the goal with `himg ▸ hemb.isOpenMap _ hopen` or `rw [himg]`. This replaces the opaque `convert` with a named equality.

Benefit: The geometric content (the open solid torus maps onto the radius-`r` tube) becomes a visible statement. A breakage then points to the equality being proved, not to a side goal produced by `convert`.

Source evidence:

- `TauCeti.exists_isOpenEmbedding_normalTube` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Geometry/Manifold/TubularNeighborhood/Euclidean.lean`: IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2)

### fragile-proofs: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L269-L270)

Declaration: `TauCeti.exists_forall_notMem_span_tangentVector`

The proof extracts `ContDiff ℝ 1 (deriv _)` from `contDiff_succ_iff_deriv` using the positional projection `.2.2` into the three-part conjunction `Differentiable ∧ (n = ω → AnalyticOn ..) ∧ ContDiff n (deriv f)`. It also applies `ContDiff.differentiable` with `one_ne_zero` for the `1 ≠ 0` side condition. Adding or reordering a conjunct, which is plausible for this lemma since the `ω` clause was recently added, would silently break the projection. The hypothesis is stated as `1 + 1`, so `n` is only recovered by unification.

Proposed change:

Avoid the conjunction projection. For example, use `hγ.iterate_deriv'` or a more direct fact. Alternatively, destructure with named components, `obtain ⟨-, -, hd'⟩ := contDiff_succ_iff_deriv.mp hγ`, which is easier to repair. Or use `contDiff_one_iff_deriv`-style lemmas that expose the needed `ContDiff ℝ 1 (deriv _)` more directly.

Benefit: The proof no longer relies on the index of a conjunct. A change to the lemma's shape then fails at an easily understood place.

Source evidence:

- `contDiff_succ_iff_deriv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean`: ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n = ω → AnalyticOn 𝕜 f univ) ∧

### fragile-proofs: [TauCeti/ModelTheory/Scott/RigidGraph.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L90-L96)

Declaration: `TauCeti.bfEquiv_two_rigidSixGraph_iff`

The proof rewrites the hypothesis and then reads the components of `BFEquiv.add_one`'s right-hand side by position (`h.2.1 x`, `h.2.2 y`). It therefore depends on the exact nesting and order of that conjunction. If a conjunct is added, reordered or regrouped (for example a flatter shape, or a different order of forth and back), these projections break or silently pick the wrong component. Other files in the library destructure the same lemma with named pattern variables.

Proposed change:

Obtain the components by name instead of projecting. For example, `obtain ⟨-, hforth, hback⟩ := (BFEquiv.add_one (1 : Ordinal.{o}) _ _).mp (by simpa only [one_add_one_eq_two] using h)`. Then use `hforth x` and `hback y` in the two cases. The `norm_num` rewrite of `2` can also be replaced by `← one_add_one_eq_two`, as the file does later at line 133.

Benefit: The dependence on the shape of `BFEquiv.add_one` is stated once, in the pattern. This matches the style used elsewhere in the library and keeps the case split readable.

Source evidence:

- `TauCeti.BFEquiv.add_one` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/BackAndForth/Equivalence.lean`: BFEquiv (L := L) α n a b ∧
      (∀ x : M, ∃ y : N, BFEquiv (L := L) α (n + 1) (snoc a x) (snoc b y)) ∧
- `TauCeti.BFEquiv.comp` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/BackAndForth/Equivalence.lean`: obtain ⟨h, hforth, hback⟩ := (add_one α a b).mp h

### fragile-proofs: [TauCeti/ModelTheory/Scott/RigidGraph.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L132-L134)

Declaration: `TauCeti.orbitRank_rigidSixGraph`

This is a five-step rewrite chain on the goal `2 ≤ orbitRank ...`. `← one_add_one_eq_two` rewrites every `2` in the goal, and each later step needs the previous one to leave a syntactic match. For example, `lt_iff_not_ge` has to produce `¬ orbitRank _ ≤ 1` in exactly the form `orbitRank_le_iff` expects. A routine change would break the chain: restating `2` differently, or changing the order or implicit form of `Order.add_one_le_iff`.

Proposed change:

Prove the lower bound as an explicit step. Use `by_contra hlt`, then `have : orbitRank (L := Language.graph) (fun _ : Fin 1 => v) ≤ 1 := Order.lt_two_iff_le_one ▸ not_le.mp hlt`, but only with lemma names verified in Mathlib. Then apply `(orbitRank_le_iff _ _).mp this` to get orbit stability at 1. Alternatively, state a small helper lemma `1 ∉ orbitStable a` for these vertices and conclude with `orbitRank_le_iff` and `not_le`. Each step then cites one named lemma and does not depend on a global `2` rewrite.

Benefit: A change to one numeral or lemma statement then breaks one local step instead of the whole chain. The mathematical content, that orbit rank is not at most 1 because level 1 is not orbit-stable, is also stated directly.

Source evidence:

- `TauCeti.orbitRank_le_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/Scott/Rank.lean`: orbitRank (L := L) a ≤ α ↔ α ∈ orbitStable (L := L) a
- `TauCeti.mem_orbitStable_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/Scott/Rank.lean`: α ∈ orbitStable (L := L) a ↔
      ∀ b : Fin n → M, BFEquiv (L := L) α n a b →

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

### fragile-proofs: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L255-L268)

Declaration: `integral_seg1_eq_neg_log / integral_seg3_eq_log (and the `h2` step in log_cancellation)`

The final steps are closed by bare `simp_all`. The result depends on the simp set containing `integral_inv_of_pos` with its side conditions, then `div_eq_inv_mul`/`Real.log_inv`/`one_div`, all discharged from the local hypotheses. In `integral_seg3_eq_log` and in `h2` of `log_cancellation` (line 297), `simp_all` also rewrites the other hypotheses (`h1`, `h_sub`, `this`). Adding or removing a simp lemma, or changing the normal form of `Real.log (1/ε)` or `Real.log (1 / (ε / r))`, can break these proofs, and the failure would be hard to diagnose. The same file already proves the analogous statement with an explicit chain, in `h1` of `log_cancellation`.

Proposed change:

Replace `simp_all` with the explicit rewrite already used in `log_cancellation`: `rw [integral_inv_of_pos hε one_pos, Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub]` for the first lemma. For `integral_seg3_eq_log` and `h2`, finish with `rw [h1]` (or `rw [h_sub]`) followed by the same `integral_inv_of_pos` chain, and a final `neg_neg` or `Real.log_one`-style step, instead of `simp_all`. Alternatively, derive `integral_seg3_eq_log` from `integral_seg1_eq_neg_log`.

Benefit: The proofs depend only on named lemmas, so they survive simp-set changes. A reader can see where `log (1/ε) = -log ε` is used. The `simp_all` calls in `log_cancellation` can no longer silently rewrite unrelated hypotheses.

Source evidence:

- `log_cancellation` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: rw [integral_inv_of_pos hεr_pos one_pos, Real.log_div one_ne_zero (ne_of_gt hεr_pos),
      Real.log_one, zero_sub]
- `intervalIntegral.integral_inv_of_pos` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`: theorem integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x in a..b, x⁻¹ = log (b / a)

### fragile-proofs: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L358-L363)

Declaration: `pv_cutoff_F_integrable_delta_1 (same pattern in the other pv_cutoff_* lemmas and in pv_sector_cutoff_eq, lines 319, 336, 359, 382, 414, 505, 528, 559, 597, 606)`

The proofs rewrite with `rw [ite_eq_left]`, leaving the condition as an implicit side goal, and then rely on the order of the resulting goals. The `ite_eq_right (not_lt.mpr _)` variants leave a metavariable `_` to be filled by a later goal. The bullets that follow assume that the main goal comes first and the condition second. They also assume that `dsimp only [F]; simp only [sub_zero]` leaves the `ite` in exactly the form `if ‖…‖ > ε then … else 0`. Routine changes would break this: a different goal-ordering convention in `rw`, a change in how `>` is displayed or unfolded by `simp only [sub_zero]`, or a change in `Decidable` instance elaboration (the file uses `Classical.propDecidable`). The same fragile three-step prelude is copy-pasted about ten times.

Proposed change:

Prove the condition first as a named hypothesis, e.g. `have hgt : ‖sectorCurve r α t‖ > ε := by rw [sectorCurve_norm_seg1 …]; calc …`. Then close the goal with `simp only [F, sub_zero, if_pos hgt]` or `show (if _ then _ else _) = _; rw [if_pos hgt]`. Use `if_neg (not_lt.mpr hle)` with `hle` established beforehand in the zero-region cases. Better still, factor out two small lemmas: one for `F t = (sectorCurve …)⁻¹ * deriv … ` when `ε < ‖sectorCurve r α t‖`, and one for `F t = 0` otherwise. All the segment proofs can then use these.

Benefit: The proofs no longer depend on goal ordering or on metavariable placeholders in `rw`. The mathematical content (norm > ε on the region) is stated before it is used. The copy-pasted prelude is replaced by a single reusable interface.

Source evidence:

- `ite_eq_left` in `/home/kim/.elan/toolchains/leanprover--lean4---v4.35.0-rc3/src/lean/Init/Core.lean`: theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t
- `pv_cutoff_F_integrable_0_delta` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: dsimp only [F]; simp only [sub_zero]; rw [ite_eq_right (not_lt.mpr _)]

### fragile-proofs: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L648-L650)

Declaration: `pv_sector_dz_over_z`

The final step uses `unfold cauchyPrincipalValue'` and then `exact h_tendsto.limUnder_eq`. This requires the unfolded `limUnder` expression to match `h_tendsto`'s function syntactically, including the `ite` form, the `‖γ t - z₀‖` shape with `z₀ = 0`, and `f (γ t)` being beta-reduced. The proof therefore depends on the internal body of the definition. A change to how `cauchyPrincipalValue'` is stated (for example `≥` versus `>`, an explicit `Set.indicator`, or `z₀` handling) breaks it, even though the existence of a limit is already established by the first component of the conjunction.

Proposed change:

Prove the value through the public interface: first obtain `hex : CauchyPrincipalValueExists' …` and use the API connecting the existence predicate to the value, or add one lemma `CauchyPrincipalValueExists'.tendsto_cauchyPrincipalValue'` (or `cauchyPrincipalValue'_eq_of_tendsto`) in Basic.lean. Then conclude with `cauchyPrincipalValue'_eq_of_tendsto h_tendsto`. At minimum, use `show limUnder _ _ = _` or `Tendsto.limUnder_eq` after `simp only [cauchyPrincipalValue']`, and state `h_tendsto` against the definition's own expression.

Benefit: Changes to the definition's integrand, such as a switch to `Set.indicator`, would no longer require re-proving the value statement in every file that computes a PV. The proof states what it uses: a limit equals the `limUnder` value.

Source evidence:

- `cauchyPrincipalValue'` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Basic.lean`: limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

### fragile-proofs: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L570-L579)

Declaration: `fourier_poitouVerticalProfileDerivative_regularized (also fourier_poitouVerticalProfileSecondDerivative_regularized)`

The final step is `simp_all` over the whole context (`hderiv`, `h`, `hδ`, and others). In effect it rewrites `h` with `hderiv` and then closes the goal with `h`. That is a two-step explicit argument. `simp_all` also simplifies the goal and every hypothesis against each other, so a routine simp-set change (e.g. a new simp lemma on `smul`, `𝓕` or `I`) could rewrite `h` and the goal into different normal forms. The same pattern is repeated at line 1210.

Proposed change:

Replace the closing `simp_all` with `rw [hderiv] at h; exact h`. `Real.fourier_deriv` concludes `𝓕 (deriv f) = fun x ↦ (2 * π * I * x) • 𝓕 f x`, which is already the statement after rewriting. Equivalently, `simpa only [hderiv] using h`. Do the same at line 1210.

Benefit: The proof names exactly what is used (`hderiv` and `Real.fourier_deriv`). It no longer depends on simp-set behaviour or the surrounding context, and it is easier to repair if a lemma changes.

Source evidence:

- `Real.fourier_deriv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Fourier/FourierTransformDeriv.lean`: 𝓕 (deriv f) = fun (x : ℝ) ↦ (2 * π * I * x) • (𝓕 f x)
- `fourier_poitouVerticalProfileSecondDerivative_regularized` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:         rw [hderiv]
        exact
          poitouVerticalProfileSecondDerivative_regularized_integrable

### fragile-proofs: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L1238-L1251)

Declaration: `sq_abs_mul_norm_poitouTransform_regularized_le (hfactor/hnorm)`

`hnorm` is just `hfourier` followed by `norm_smul` and `hfactor`, but it is proved with `simp_all` in a context holding `hfourier`, `hfactor`, `hδ` and the `let w`. The result depends on simp orientation: `hfourier` is used as a rewrite rule, `hfactor` has a norm-of-power left side that simp may normalise first, and the unfolding of `w` could change. `hfactor` itself uses `norm_num; field_simp; simp`, where the goal shape after each step is unknown.

Proposed change:

Prove `hnorm` explicitly: `rw [hfourier, norm_smul, hfactor]`. In `hfactor`, avoid the non-terminal `norm_num` and `field_simp` chain. For example, rewrite `‖2 * π * I * w‖`, using `Complex.norm_real` and `abs_of_pos Real.pi_pos`, to `|t|`, then use `div_mul_cancel₀` (or a `field_simp` as the last tactic) to close the goal.

Benefit: The dependency on `hfourier` and `hfactor` becomes visible. Changes to simp lemmas or `norm_num` extensions will not silently break the step.

Source evidence:

- `fourier_poitouVerticalProfileSecondDerivative_regularized_eq_sq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: ((2 * Real.pi * I * w) ^ 2) •
        𝓕 (regularizedPoitouVerticalProfile y δ σ) w

### fragile-proofs: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L384-L392)

Declaration: `norm_poitouVerticalProfileDerivative_regularized_le and norm_poitouVerticalProfileSecondDerivative_regularized_le (norm computation steps)`

After `simp only [...]` the proof calls a non-terminal `norm_num`. It then supplies `hnorm` and runs `rw [hnorm]`, which only works if `norm_num` leaves exactly the subterm `‖(σ : ℂ) - 1 / 2‖`. `norm_num` is free to normalise that term (push casts, rewrite `1/2` or `σ - 1/2`) or to reorder the surrounding products and sums. A routine simp/norm_num update can then make `rw [hnorm]` fail with 'motive/pattern not found'. The same fragile pattern is repeated at lines 1036–1046, where `norm_num` is followed by `grind` using a hypothesis that was not passed explicitly.

Proposed change:

Prove `hnorm` and the exponential norm `‖Complex.exp ((σ - 1/2) * x)‖ = Real.exp ((σ - 1/2) * x)` first. Pass them to the `simp only [...]` list (or `rw` them), and drop the intermediate `norm_num`. Concretely, state `hnorm : ‖(((σ - 1/2 : ℝ)) : ℂ)‖ = a` with the cast pushed in the same form as the profile definition. Then close the inequality with `simp only [norm_mul, hnorm, ...]`, or `rw [norm_mul, norm_mul, Complex.norm_real, ...]`, followed by `calc` or `gcongr`. The two blocks can also share one lemma bounding `‖poitouVerticalProfileDerivative …‖` pieces.

Benefit: The proof no longer relies on the opaque normal form produced by `norm_num`. It states the norm identities it uses, and the duplicated blocks can share them.

Source evidence:

- `norm_poitouVerticalProfileSecondDerivative_regularized_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:           norm_num
          have hnorm :
              ‖((σ : ℂ) - 1 / 2)‖ = a := by

### fragile-proofs: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L926-L937)

Declaration: `poitouVerticalProfileDerivative_regularized_integrable and integrable_quadratic_abs_mul_exp_neg_mul_sq (hone/htwo)`

The `hone` and `htwo` integrability facts are obtained with `simp_all`, which must turn `‖x * exp (-b*x^2)‖` into `|x| * exp (...)`, and also turn `|x| ^ (2:ℝ)` into `x ^ 2` (the `rpow` form). Neither step is spelled out, and `simp_all` also touches the other hypotheses `hzero`, `hb`, etc. The `x ^ (2:ℝ)` to `x ^ 2` conversion goes through simp lemmas such as `Real.rpow_two` (or `rpow_natCast`). A renamed or removed simp lemma, or a changed normal form for `‖x * y‖`, would break these proofs in an unobvious way. The same pattern appears at line 449 for `hone`.

Proposed change:

Use `h.congr (ae_of_all _ fun x ↦ by simp [norm_mul, Real.rpow_two])` (or `Integrable.congr` with an explicit pointwise `Real.norm_eq_abs`/`mul_assoc` rewrite) in place of `simp_all`. Alternatively, finish with `simpa [norm_mul, Real.rpow_two] using h`. The goal is then rewritten using a stated list of lemmas rather than by whole-context simplification.

Benefit: The conversion from `‖·‖` and `rpow` forms to `|x|` and `x^2` is explicit. A failure points at one lemma instead of at a context-wide `simp_all`.

Source evidence:

- `integrable_quadratic_abs_mul_exp_neg_mul_sq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: (integrable_rpow_mul_exp_neg_mul_sq hb
        (s := 2) (by norm_num)).const_mul C
    simp_all

### fragile-proofs: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L202-L207)

Declaration: `abs_sinh_le_cosh`

`habssq` is `hsq` with `sq_abs` applied, but it is proved by `simp_all` with `hid : cosh x ^ 2 - sinh x ^ 2 = 1` in the context. `simp_all` may rewrite `hsq` and the goal using `hid`, and `hid` using `hsq`, so the result depends on how simp orients and uses these related hypotheses. This is a needless sensitivity for a one-lemma step.

Proposed change:

Replace with `by rwa [sq_abs]`. Better still, replace the whole proof with `abs_le_of_sq_le_sq'`-style lemmas or `sq_le_sq'`. For example, `abs_le.mpr ⟨by nlinarith [Real.cosh_pos x, Real.sinh_lt_cosh x], (Real.sinh_lt_cosh x).le⟩` (check the names `Real.sinh_lt_cosh` and `abs_le` before using them).

Benefit: The proof depends only on `sq_abs`. It does not depend on the whole-context simp behaviour.

Source evidence:

- `abs_sinh_le_cosh` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:   have hid := Real.cosh_sq_sub_sinh_sq x

### fragile-proofs: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L61-L65)

Declaration: `CKN.Foundation.Parabolic.Morrey.cylinderAbsIntegral_le_morreyNorm`

The final step relies on `simpa [mul_comm]` to reconcile the lemma's output with the goal. In the pinned Mathlib, `mul_le_mul_left bc a : b * a ≤ c * a`. The goal has the multiplier on the left, `r^α * (r^(-α) * I) ≤ r^α * N`. The lemma name suggests the opposite orientation, and an older Mathlib had the two names swapped. The proof compiles only because `mul_comm` flips the products in both the goal and the hypothesis. A change to simp-set normal forms or to the left/right naming would break it, and the failure would be hard to diagnose.

Proposed change:

Prove this step directly with the intended orientation. Use `mul_le_mul_right hcell' ((ENNReal.ofReal r) ^ (5 * (1 - 1 / q)))`, which in this Mathlib gives `a * b ≤ a * c` for `bc : b ≤ c`. Alternatively use `by gcongr`, or `mul_le_mul' le_rfl hcell'`. Both avoid dependence on the left/right naming, and no `simpa` is needed.

Benefit: The monotonicity step becomes a plain term. It no longer depends on `mul_comm` normalisation or on which of `mul_le_mul_left`/`mul_le_mul_right` currently has which shape.

Source evidence:

- `mul_le_mul_left` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`: theorem mul_le_mul_left [i : MulRightMono α] (bc : b ≤ c) (a : α) : b * a ≤ c * a :=
- `mul_le_mul_right` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`: theorem mul_le_mul_right [MulLeftMono α] (bc : b ≤ c) (a : α) : a * b ≤ a * c :=

### fragile-proofs: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L227-L229)

Declaration: `CKN.Foundation.Parabolic.Morrey.positive_shell_integral_le (hprod)`

The goal is `kernel * |f| ≤ bound * |f|`, a multiplication on the right. The lemma `mul_le_mul_right` in this Mathlib produces `|f| * kernel ≤ |f| * bound`, so the proof uses `simpa [mul_comm]` to bridge the mismatch. The proof therefore depends on the swapped `left`/`right` naming and on simp's commutativity normalisation. A rename or a change in how simp orders the products would break it. The goal also goes through the pointwise form of `setLIntegral_mono_ae`, which makes the unfolded term harder to see.

Proposed change:

Use the lemma whose shape matches the goal, `mul_le_mul_left (hkernel w hw) (ENNReal.ofReal |f w|)`, which in this Mathlib gives `b * a ≤ c * a`. Alternatively use `by gcongr` or `mul_le_mul_right' (hkernel w hw) _`. In every case drop `simpa [mul_comm]`.

Benefit: The step no longer depends on simp's AC normalisation or on the swapped lemma naming. It states the pointwise monotonicity directly.

Source evidence:

- `mul_le_mul_left` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`: theorem mul_le_mul_left [i : MulRightMono α] (bc : b ≤ c) (a : α) : b * a ≤ c * a :=
- `positive_shell_integral_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: (mul_le_mul_right (hkernel w hw) (ENNReal.ofReal |f w|))

### fragile-proofs: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L265-L267)

Declaration: `CKN.Foundation.Parabolic.Morrey.positive_shell_integral_le (final calc step)`

This step uses `simpa` with `mul_comm`, `mul_left_comm` and `mul_assoc` together. That amounts to an ad-hoc AC normalisation of both the goal and the hypothesis. The lemma `mul_le_mul_left hF c` yields `(∫…) * c ≤ (…) * c`, but the goal is `c * (∫…) ≤ c * (…)`. The proof depends on simp's chosen ordering for the product, including how it handles the `ENNReal.ofReal (2*b) ^ _ * morreyNorm` term. A change to simp lemmas or to `ofReal`/`rpow` simp normal forms could make the two sides normalise differently, or turn it into a `simp` loop or failure. The term is also not stated against the intended orientation.

Proposed change:

Replace the `simpa` with the lemma of the correct shape. Use `mul_le_mul_right hF ((ENNReal.ofReal a) ^ (-(5 - β)))`, which in this Mathlib gives `a * b ≤ a * c`. This matches the goal `c * ∫ ≤ c * (…)`. Alternatively use `by gcongr`.

Benefit: The inequality is exactly the stated `c * x ≤ c * y` step with no AC normalisation. This removes a sensitive simp call that also rewrites inside the `ENNReal.ofReal`/`rpow` subterms.

Source evidence:

- `mul_le_mul_right` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`: theorem mul_le_mul_right [MulLeftMono α] (bc : b ≤ c) (a : α) : a * b ≤ a * c :=
- `mul_le_mul_left` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`: theorem mul_le_mul_left [i : MulRightMono α] (bc : b ≤ c) (a : α) : b * a ≤ c * a :=

### fragile-proofs: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L122-L127)

Declaration: `RS.taylorCoeffAt_add`

The proof rewrites to `(p + q).coeff j = p.coeff j + q.coeff j` and closes it with a bare `rfl`. That works only by unfolding `FormalMultilinearSeries.coeff` and the `Add` instances on `FormalMultilinearSeries` and `ContinuousMultilinearMap`. Mathlib states the series-level fact as `FormalMultilinearSeries.add_apply`, but the proof does not use it. A routine change to the `Add` instance, to `coeff`, or to the reducibility of either would break the `rfl`.

Proposed change:

Replace the final `rfl` with a step that goes through the public lemma. For example, unfold `FormalMultilinearSeries.coeff` and use `FormalMultilinearSeries.add_apply` together with `ContinuousMultilinearMap.add_apply`, as in `simp [FormalMultilinearSeries.coeff, FormalMultilinearSeries.add_apply]`. Alternatively, prove a small local lemma `coeff_add` once, using those lemmas, and call `rw [coeff_add]`. I have not compiled this.

Benefit: The additivity proof no longer depends on the defeq unfolding of `coeff` and `Add`. It names the lemma that justifies the step, so it is easier to read and survives refactors of those definitions.

Source evidence:

- `FormalMultilinearSeries.add_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean`: theorem add_apply (p q : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : (p + q) n = p n + q n := rfl
- `FormalMultilinearSeries.coeff` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/FormalMultilinearSeries.lean`: def coeff (p : FormalMultilinearSeries 𝕜 𝕜 E) (n : ℕ) : E :=

### fragile-proofs: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L102-L107)

Declaration: `scalarTorusRepresentative_memL2On (local `hequiv`)`

The identity `equiv.symm x = toUnitTorus 2 x.1` is proved by injecting through `equiv` and closing with `rfl`. That `rfl` only works by reducing `equiv (equiv.symm x)` and `equiv (toUnitTorus 2 x.1)` through the internals of `measurableEquivPiIoc`: `piCongrRight`, `subtypePiEquivPi.symm`, `AddCircle.measurableEquivIoc` and `equivIoc`. A routine refactor of how these equivalences are built, such as a different `trans` structure or an `equivIoc` defined via `toIocMod`, could stop the definitional unfolding from going through. Mathlib already exposes this fact as a public, simp-tagged lemma, so the proof does not need the internals.

Proposed change:

Replace the whole `hequiv` proof with the public lemma, e.g. `UnitAddTorus.coe_symm_measurableEquivPiIoc_apply x`. Its statement is `(measurableEquivPiIoc b).symm y = fun i => (y.1 i : UnitAddCircle)`. The right-hand side is `AVenhance.Infra.Torus.toUnitTorus 2 x.1` after unfolding the short definition `toUnitTorus`, so `by simpa [AVenhance.Infra.Torus.toUnitTorus] using ...` or `(UnitAddTorus.coe_symm_measurableEquivPiIoc_apply x)` should close it. Alternatively, go through `AVenhance.Infra.Torus.unitTorusRepresentative_eq_of_mem_unitCell x.2`.

Benefit: The proof depends on the documented API of `measurableEquivPiIoc` instead of how it is built. The injectivity detour and `rfl` disappear, and the reader sees directly that `equiv.symm` is the coordinatewise quotient map.

Source evidence:

- `UnitAddTorus.coe_symm_measurableEquivPiIoc_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Fourier/AddCircleMulti.lean`: (measurableEquivPiIoc b).symm y = fun i => (y.1 i : UnitAddCircle) := rfl
- `AVenhance.Infra.Torus.toUnitTorus` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: fun i => (x i : UnitAddCircle)

### fragile-proofs: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L93-L96)

Declaration: `scalarTorusRepresentative_memL2On (`hmeasureTorus`)`

The measure-preservation of `equiv` is obtained by `change`-ing the goal to a `comap` form and then running `simpa` with unfolded local `let`s and the project's `unitCell`/`unitCellAt` definitions. This depends on simp normalising the subtype `{x // ∀ i, x i ∈ Ioc ..}` and the `Ioc (0) (0+1)` bounds into exactly the shape of `measurePreserving_equivPiIoc`. Changing the form of `unitCellAt` (for example `Ioc a (a+1)` to `Ioc a (1+a)`) or a simp-set change such as `zero_add` normalisation would break it with an opaque `simpa` failure.

Proposed change:

Make the cell subtype exactly Mathlib's `{x : Fin 2 → ℝ // ∀ i, x i ∈ Ioc (0) (0 + 1)}`, or add a small lemma in `Torus/Basic.lean` stating `MeasurePreserving (measurableEquivPiIoc a) volume (volume.comap Subtype.val)` for `unitCellAt`. Then `hmeasureTorus` becomes `exact` of that lemma, with no `simpa` over definitions.

Benefit: The bridge between Mathlib's Ioc-subtype statement and the project's `unitCellAt` is stated once as an explicit lemma instead of being rediscovered by simp in each use. A change to the cell definition then fails at one clearly named place.

Source evidence:

- `UnitAddTorus.measurePreserving_equivPiIoc` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Fourier/AddCircleMulti.lean`: MeasurePreserving (measurableEquivPiIoc a) volume (Measure.comap Subtype.val volume)
- `AVenhance.Infra.Torus.unitCellAt` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)}

### fragile-proofs: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L217-L221)

Declaration: `weakPathRepresentative_pairing_eq_inner and FrozenDriftProblem.initial_pairing_eq_cell_integral`

Both pairing proofs rewrite with a `show ... from rfl` claiming `periodicToTorus (fun y => g y * ψ y) x = periodicToTorus g x * periodicToTorus ψ x`. This holds only by unfolding the definition of `periodicToTorus`, and the same inline defeq is copied at line 255. If `periodicToTorus` stops being a plain `fun x => f (rep x)` (for example gets a structure wrapper or an argument change), both places break. Each copy also needs the long explicit expression restated.

Proposed change:

Add one lemma next to `periodicToTorus` in `Torus/Basic.lean`, e.g. `periodicToTorus_mul (f g : Vec d → ℝ) : periodicToTorus (fun y => f y * g y) = fun x => periodicToTorus f x * periodicToTorus g x := rfl`. Use it in both places instead of the inline `show ... from rfl`. The `rw` is then a simple `periodicToTorus_mul`, and the defeq is isolated in one spot next to the definition.

Benefit: The unfolding dependency is local to the definition's file. The two proofs get shorter and stop restating long terms, and changes to `periodicToTorus` need one fix instead of several.

Source evidence:

- `AVenhance.Infra.Torus.periodicToTorus` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: fun x => f (unitTorusRepresentative d x)
- `FrozenDriftProblem.initial_pairing_eq_cell_integral` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: AVenhance.Infra.Torus.periodicToTorus P.θ₀ x *

### fragile-proofs: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L51-L100)

Declaration: `planeCurveToBivariate_X_zero / planeCurveToBivariate_X_one / planeCurveToBivariate_C`

The helper facts `hinner` are proved by rewriting with `MvPolynomial.finSuccEquiv_apply`. That exposes the `eval₂Hom`/`Fin.cases` implementation of `finSuccEquiv`, and the X_one case then needs `rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide]` followed by `rfl`. Mathlib already has `finSuccEquiv_X_zero` and `finSuccEquiv_X_succ`, so the public interface exists. Each lemma then uses `change Polynomial.map ... .toRingHom (...)` to see through `AlgEquiv.trans` and `mapAlgEquiv` by definitional unfolding. Re-defining `finSuccEquiv` (it is a `trans` of `renameEquiv` and `optionEquivLeft`) or changing `mapAlgEquiv` would break these proofs, even though the statements stay true.

Proposed change:

Prove `hinner` with the existing lemmas: `MvPolynomial.finSuccEquiv_X_zero` for X_zero, and `MvPolynomial.finSuccEquiv_X_succ (j := 0)` for X_one after one `show (1 : Fin 2) = Fin.succ 0` rewrite. Replace the `change Polynomial.map ...` steps with `simp [planeCurveToBivariate, hinner]`, or `rw [planeCurveToBivariate, AlgEquiv.trans_apply, hinner, Polynomial.coe_mapAlgEquiv]`. `Polynomial.coe_mapAlgEquiv` states `⇑(mapAlgEquiv f) = map f`. Then finish with `Polynomial.map_X` / `Polynomial.map_C`.

Benefit: The proofs would depend on the stated simp-level API of `finSuccEquiv` and `Polynomial.mapAlgEquiv`, not on how `Fin.cases`, `eval₂Hom` and `AlgEquiv.trans` reduce. They would survive a refactor of those definitions.

Source evidence:

- `MvPolynomial.finSuccEquiv_X_succ` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/MvPolynomial/Equiv.lean`: theorem finSuccEquiv_X_succ {j : Fin n} : finSuccEquiv R n (X j.succ) = Polynomial.C (X j)
- `MvPolynomial.finSuccEquiv_X_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/MvPolynomial/Equiv.lean`: theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X
- `Polynomial.coe_mapAlgEquiv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Polynomial/AlgebraMap.lean`: theorem coe_mapAlgEquiv (f : A ≃ₐ[R] B) : ⇑(mapAlgEquiv f) = map f

### fragile-proofs: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L135-L170)

Declaration: `bivariateEquiv_symm_natDegree_eq_degreeOf_one`

The proof builds an ad hoc `Unique {i : Fin 2 // i ≠ 1}` instance and a `q` from `optionEquivLeft` and `rename (Equiv.optionSubtypeNe 1).symm`. It then proves `lhs = rhs` by `fin_cases i <;> simp [lhs, rhs, q, e, remaining]`. This depends on the definitional shape of `equivMvPolynomial` (an `ofAlgHom` of `aevalAeval`), on how `optionSubtypeNe` evaluates at the two generators, and on `simp` unfolding the local `remaining` abbreviation. A change in the simp set for `Equiv.optionSubtypeNe` or `optionEquivLeft`, or a different instance for `Unique`, would break the simp calls without any change in the mathematics. The file already proves `transposeBivariate_planeCurveToBivariate` and `planeCurveToBivariate_natDegree_eq_degreeOf_zero`, which give the coordinate-1 degree through a swap.

Proposed change:

Derive the statement from the already proved `planeCurveToBivariate_natDegree_eq_degreeOf_zero` plus a degree lemma for `transposeBivariate`, using `transposeBivariate_planeCurveToBivariate`. Alternatively, prove the symmetric statement for `degreeOf 1` by renaming the two variables with `Equiv.swap`. This uses the already proved coordinate-0 lemma and removes the local `Unique` instance and the `remaining` subtype.

Benefit: The two degree facts would share a single `finSuccEquiv`-based argument. The proof would no longer reach into `optionSubtypeNe`/`optionEquivLeft` internals through `fin_cases ... simp [..., remaining]`.

Source evidence:

- `Polynomial.Bivariate.equivMvPolynomial` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Polynomial/Bivariate.lean`: .ofAlgHom (aevalAeval (.X 0) (.X 1)) (MvPolynomial.aeval ![.C X, X])
- `transposeBivariate_planeCurveToBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: (Polynomial.Bivariate.equivMvPolynomial K).symm f

### fragile-proofs: [LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L85-L87)

Declaration: `EulerMeanHarmonic.localL2Energy_ball_le_of_ae_bound`

After `rw [setIntegral_const, smul_eq_mul]` the goal contains `volume.real (ball 0 r) * C`. Mathlib's `setIntegral_const` states its result with `μ.real s • c`. The proof then uses a `change` to the `.toReal` form, which relies on `Measure.real` being definitionally `(μ s).toReal`. The `change` target also spells out the exact goal shape, so it breaks if `setIntegral_const` or `smul_eq_mul` produce a different shape. Mathlib supplies a public rewrite lemma, `measureReal_def`, for exactly this conversion, so the proof does not need to depend on the definition's unfolding.

Proposed change:

Replace the `change` with the public lemma. For example: `rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal r hr]; ring`. Alternatively, state a `volume.real` version of `volume_ball_toReal` and rewrite with that directly.

Benefit: The proof no longer relies on defeq unfolding of `Measure.real`, and no longer restates the goal. If `Measure.real` is made irreducible or changes its definition, only `measureReal_def` has to change.

Source evidence:

- `MeasureTheory.measureReal_def` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean`: μ.real s = (μ s).toReal := rfl
- `MeasureTheory.setIntegral_const` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`: ∫ _ in s, c ∂μ = μ.real s • c
- `EulerMeanHarmonic.volume_ball_toReal` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/NavierStokesAndEuler/Euler/MeanHarmonicSmallBall.lean`: (volume (Metric.ball (0 : Space) r)).toReal = r ^ 3 * (Real.pi * 4 / 3)

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

### repeated-proof-machinery: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293)

Declaration: `Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow / Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow`

The two theorems have the same proof. Both take `hf.mul hg`, then use `Eventually.isBigO`. Both then prove `‖t^a * t^b‖ ≤ ‖t^c‖` for `1 ≤ t` with the same four steps: `Real.rpow_add`, `Real.norm_of_nonneg`, `Real.rpow_nonneg`, `Real.rpow_le_rpow_of_exponent_le`. The ℕ version differs only by a cast step, `replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht`. The real analytic content is therefore written twice.

Proposed change:

Add a private helper that works over any filter and any real-valued map `u`:
`lemma isBigO_rpow_mul_rpow_of_le {α} {l : Filter α} {u : α → ℝ} (hu : ∀ᶠ x in l, 1 ≤ u x) (h : a + b ≤ c) : (fun x => u x ^ a * u x ^ b) =O[l] fun x => u x ^ c`.
Its proof is the current block: `Eventually.isBigO` on `hu.mono`, then `rpow_add`, `norm_of_nonneg` and `rpow_le_rpow_of_exponent_le`. The two theorems would then be `(hf.mul hg).trans (isBigO_rpow_mul_rpow_of_le (u := id) eventually_ge_atTop_1 h)` and the same with `u := Nat.cast`. For ℕ, the hypothesis comes from `tendsto_natCast_atTop_atTop.eventually_ge_atTop 1`. The `f * g` versus `fun x => ..` shape may need `Pi.mul_apply` or `.of_const_mul`.

Benefit: The pointwise rpow estimate is stated and proved once, and the ℕ/ℝ cast boilerplate disappears. The helper also covers other index types, such as sequences composed with a tendsto map. Each of the two theorems shrinks from about 8 lines to 2–3.

Source evidence:

- `Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
- `use of IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/NumberTheory/LSeries/SumCoeff.lean`: IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow

### repeated-proof-machinery: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L185-L206)

Declaration: `Complex.isBigO_cpow_rpow / Complex.isTheta_cpow_rpow`

Both proofs are three-step calc chains. Step one compares `f x ^ g x` with `‖f x‖ ^ (g x).re / exp (arg (f x) * im (g x))`. Step two divides by `isTheta_exp_arg_mul_im` using `(isTheta_refl _ _).div`. Step three removes `/ 1` with `simp only [div_one, EventuallyEq.rfl]`. Steps two and three are copied verbatim, and only the first step differs (`isBigO_of_le` versus `of_norm_eventuallyEq`).

Proposed change:

Add a lemma `isTheta_rpow_div_exp_arg_mul_im (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) : (fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) =Θ[l] fun x => ‖f x‖ ^ (g x).re`. It packages steps two and three. Then `isBigO_cpow_rpow` is `(first step).trans_isTheta (this hl)`. `isTheta_cpow_rpow` is `(Θ first step).trans (this hl_im)`. Alternatively, derive `isBigO_cpow_rpow` from the Θ statement where the hypotheses allow it.

Benefit: The division-by-bounded-exponential argument is isolated in one lemma with a clear meaning: the cpow modulus equals the rpow of the real part, up to a bounded factor. The duplicated `show α → ℝ` calc steps go away, and the two theorems differ visibly only in their first step.

Source evidence:

- `Complex.isTheta_cpow_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`:       (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)

### repeated-proof-machinery: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L316-L323)

Declaration: `Bundle.Trivialization.mk_coordChangeL and Bundle.VectorPrebundle.mk_coordChange`

`Trivialization.mk_coordChangeL` (lines 316–323) and `VectorPrebundle.mk_coordChange` (lines 858–868) are two different results with the same fragile proof. Both do `ext`, then rewrite with `mk_symm`, `coe_fst'` and `proj_symm_apply'`, apply `proj_symm_apply'` a second time, and close the side goal with `hb.2`. The first component of the goal is just the fact that `e'` preserves the base point on `⟨b, e.symm b y⟩`. That fact already exists as `Pretrivialization.mk_proj_snd'`, and `Pretrivialization.apply_mk_symm` also covers the `e.symm` side, but neither proof uses them. The proof is rederived by hand in each place.

Proposed change:

Prove the identity once at the level of the underlying data. Either add a small helper such as `Pretrivialization.mk_apply_symm_snd (e e' : Pretrivialization F (π F E)) {b} (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F) : (b, (e' ⟨b, e.symm b y⟩).2) = e' ⟨b, e.symm b y⟩`, or just apply `e'.mk_proj_snd' (x := ⟨b, e.symm b y⟩) hb.2` directly. The proof of the helper is the single lemma `mk_proj_snd'` (the point `⟨b, _⟩` has projection `b` definitionally). Then `mk_coordChangeL` becomes `by rw [coordChangeL_apply e e' hb]; exact e'.mk_proj_snd' hb.2`, and `VectorPrebundle.mk_coordChange` becomes `by rw [a.coordChange_apply he he' hb v]; exact e'.mk_proj_snd' hb.2`. `Trivialization.mk_coordChangeL` can use the `Trivialization` version of `mk_proj_snd'`, which exists at line 445 of FiberBundle/Trivialization.lean.

Benefit: This removes two copies of a 5-line `rw`/`exact` chain that depends on the exact shape of the goal after `ext`. Both lemmas shrink to two lines and say directly that the base point is preserved. If `proj_symm_apply'` or `mk_symm` change, one proof breaks instead of two.

Source evidence:

- `Bundle.VectorPrebundle.mk_coordChange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`:   · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2
- `Pretrivialization.mk_proj_snd'` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean`: theorem mk_proj_snd' (ex : proj x ∈ e.baseSet) : (proj x, (e x).2) = e x :=

### repeated-proof-machinery: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L275-L292)

Declaration: `Bundle.Trivialization.coordChangeL (continuous_toFun / continuous_invFun)`

The `continuous_toFun` and `continuous_invFun` fields of `coordChangeL` are the same argument with `e` and `e'` swapped. Each does `by_cases hb`, rewrites with `dite_eq_left`, and proves continuity of `y ↦ (e' (e.symm (b, y))).2` by composing `continuousOn_symm`, `prodMk_right`, `mk_mem_prod`, `continuousOn` and `.snd`. Otherwise it uses `continuous_id`. Each field is about 9 lines, so about 18 lines are duplicated.

Proposed change:

Prove the one-directional fact once and use it twice. For example, add a private lemma `continuous_snd_apply_symm (e e' : Trivialization F (π F E)) {b} (hb : b ∈ e.baseSet ∩ e'.baseSet) : Continuous fun y : F => (e' ⟨b, e.symm b y⟩).2`, which contains the `comp_continuous` chain once. Alternatively, make the `by_cases` a single `have key : ∀ (e e') (hb), Continuous ...` inside the definition. Then `continuous_toFun` is `key e e' hb` and `continuous_invFun` is `key e' e hb.symm`, each with the `dite_eq_left` rewrite and the `continuous_id` fallback. This also matches the symmetry already used in `symm_coordChangeL`, which swaps `hb` with `hb.symm`.

Benefit: About half of the `coordChangeL` definition disappears, and the symmetry between the two directions becomes explicit instead of being visible only by comparing two similar blocks. A change to the continuity argument is made once.

Source evidence:

- `Bundle.Trivialization.coordChangeL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`:         refine (e.continuousOn.comp_continuous ?_ ?_).snd
        · exact e'.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.2 (mem_univ y)

### repeated-proof-machinery: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L398-L456)

Declaration: `Bundle.Trivialization.continuousLinearMapAt and continuousLinearEquivAt (and symmL)`

`continuousLinearMapAt.cont` (lines 402–407) and `continuousLinearEquivAt.continuous_toFun` (lines 454–455) both prove continuity of the fiber map `y ↦ (e ⟨b, y⟩).2` with the same term. The term is `(e.continuousOn.comp_continuous (FiberBundle.totalSpaceMk_isInducing F E b).continuous fun _ => e.mem_source.mpr hb).snd`. `symmL.cont` (lines 416–424) is the analogous argument for `e.symm b`. Each definition re-derives its own fact, although the three facts form one natural statement: the trivialization restricted to a fiber is continuous in both directions.

Proposed change:

Add a lemma, for example `Trivialization.continuous_snd_mk (e : Trivialization F (π F E)) [FiberBundle F E] {b} (hb : b ∈ e.baseSet) : Continuous fun y : E b => (e ⟨b, y⟩).2`, and a companion `continuous_symm_mk` for the inverse direction. Then `continuousLinearMapAt.cont` becomes `rw [e.coe_linearMapAt b]; classical; exact continuous_if_const _ (fun hb => e.continuous_snd_mk hb) fun _ => continuous_zero`, and `continuousLinearEquivAt.continuous_toFun := e.continuous_snd_mk hb`. The `symmL.cont` proof can use the companion lemma too. The same `Continuous (fun y => (e ⟨b, y⟩).2)` pattern also appears in the `coordChangeL` fields (previous finding), where it is combined with `continuousOn_symm`.

Benefit: One named lemma gives the fiberwise continuity of a trivialization. The three definitions no longer need to unpack `totalSpaceMk_isInducing`, `mem_source` and `.snd` by hand. The benefit is smaller than for the first two findings, but it removes a repeated multi-step term and gives users a reusable lemma.

Source evidence:

- `Bundle.Trivialization.continuousLinearEquivAt` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`:     continuous_toFun := (e.continuousOn.comp_continuous
      (FiberBundle.totalSpaceMk_isInducing F E b).continuous fun _ => e.mem_source.mpr hb).snd

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

### repeated-proof-machinery: [TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L76-L82)

Declaration: `Matrix.mem_range_scalar_of_commute_specialOrthogonalGroup`

The proof ends with a generic argument that has nothing to do with the orthogonal group. Once every off-diagonal entry vanishes and the diagonal entries are all equal, M is a scalar matrix. The same assembly is repeated in the symplectic center theorem. There it appears as `refine ⟨M (Fin.castAdd m z) (Fin.castAdd m z), ?_⟩; ext a b; by_cases hab : a = b ...`, followed by `diagonal_apply_eq` and `diagonal_apply_ne` rewrites. Each proof redoes the ext/by_cases/subst/scalar_apply bookkeeping. Mathlib has `mem_range_scalar_of_commute_single` only for a commutation hypothesis. It has no lemma for the off-diagonal-zero plus constant-diagonal form.

Proposed change:

Add one helper next to the Mathlib matrix-basis lemmas, or in a TauCeti `Matrix` utilities file: `theorem mem_range_scalar_of_offDiag_eq_zero_of_diag_eq {M : Matrix n n R} (hoff : ∀ i j, i ≠ j → M i j = 0) (hdiag : ∀ i j, M i i = M j j) : M ∈ Set.range (scalar n)`. The proof would handle the empty case with `Subsingleton.elim`, otherwise pick `i` and use `⟨M i i, ext ...⟩`. The SO proof would then end with `exact mem_range_scalar_of_offDiag_eq_zero_of_diag_eq hoff hdiag`. That removes the Nonempty/card extraction and the whole ext block, since the empty case is handled inside the helper, so the `hn` card argument is only needed for hoff. The symplectic proof would end with the same call after its `hd`/`hn` argument has been turned into the all-pairs diagonal equality.

Benefit: This removes about 7 lines of ext/case bookkeeping from each proof and keeps the group-specific proofs focused on the real content. That content is the off-diagonal vanishing from half-turns and the diagonal equality from rotations. The helper is a natural characterization of scalar matrices and could be reused by future center or centralizer results for other classical groups. The saving is modest because each repeat is short.

Source evidence:

- `Matrix.mem_range_scalar_of_commute_symplectic` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Symplectic/Center.lean`:   ext a b
  by_cases hab : a = b
  · subst b
    rw [scalar_apply, diagonal_apply_eq]
- `Matrix.mem_range_scalar_of_commute_single` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Data/Matrix/Basis.lean`: theorem mem_range_scalar_of_commute_single {M : Matrix n n α}
    (hM : Pairwise fun i j => Commute (single i j 1) M) :

### repeated-proof-machinery: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L165-L248)

Declaration: `continuousOn_schwarzChristoffelBoundary / schwarzChristoffelBoundary_sub_eq / schwarzChristoffelBoundary_injOn / collinear_schwarzChristoffelBoundary_image`

Four different edge results each obtain an Edge witness `L` (from exists_tendsto_schwarzChristoffelPrimitive_sub_eq or ..._injOn_collinear). Each then re-derives, point by point, that `schwarzChristoffelBoundary a e z₀ x = L x` via `schwarzChristoffelBoundary_eq_of_tendsto ... (hL x hx)`. The transfer is done by hand each time: `congr` for continuity, a double `rw` for the increment formula, a double `rwa ... at hxy` for injectivity, and a `convert`/`ext` with two `rintro` branches for the collinear image. The identification `boundary = L` on `Ioo p q` is never stated as a lemma, so the same bookkeeping is repeated.

Proposed change:

Add one helper next to `schwarzChristoffelBoundary_eq_of_tendsto`, for example: `theorem tendsto_schwarzChristoffelPrimitive_boundary_of_mem_Ioo (a e) (z₀) {p q} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) : ∀ x ∈ Ioo p q, Tendsto (schwarzChristoffelPrimitive a e z₀) (𝓝[upperHalfPlaneSet] (x:ℂ)) (𝓝 (schwarzChristoffelBoundary a e z₀ x))`. Better, state the Edge package with `L := schwarzChristoffelBoundary a e z₀`: `∃ L, EqOn (schwarzChristoffelBoundary a e z₀) L (Ioo p q) ∧ ContinuousOn L (Ioo p q) ∧ (increment formula) ∧ InjOn L (Ioo p q) ∧ Collinear ℝ (L '' Ioo p q)`. Alternatively, prove once that `hB : EqOn (schwarzChristoffelBoundary a e z₀) L (Ioo p q)`. The four proofs then reduce to `hLcont.congr hB`, `rw [hB hx, hB hy]; exact hsub ..`, `hLinj.congr hB.symm` (using `InjOn.congr`), and `hB.image_eq ▸ hLcol` (using `Set.EqOn.image_eq`). This removes the `ext`/`rintro` collinear block and the duplicated `rw`/`rwa` chains.

Benefit: The relation 'on a prevertex-free interval the canonical boundary map is Edge's continuous extension L' is proved once instead of four times. The four downstream proofs shrink to one-liners, and the collinear proof loses its two-direction set-extensionality block. Any later edge-property transfer, for example the derivative or the Icc continuity, can reuse the same identification.

Source evidence:

- `TauCeti.exists_tendsto_schwarzChristoffelPrimitive_injOn_collinear` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Edge.lean`: InjOn L (Ioo p q) ∧ Collinear ℝ (L '' Ioo p q)
- `TauCeti.exists_tendsto_schwarzChristoffelPrimitive_sub_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Edge.lean`: (∀ x ∈ Ioo p q, Tendsto (schwarzChristoffelPrimitive a e z₀)
- `TauCeti.schwarzChristoffelBoundary_injOn` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`: rwa [schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx),

### repeated-proof-machinery: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L104-L133)

Declaration: `TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg`

The proof repeats three pieces of machinery that also appear in Normalization.lean. (1) The non-vanishing proof of B(x γ, x (-γ)) is copied verbatim. (2) The step that takes the cyclic symmetry for the triple (γ, -α, β) and rewrites it with `structureConstant_skew` to relate N(-α,-β)·B_γ to -N(-α,γ)·B_β is also done in `structureConstant_neg_add_mul_killingForm_eq`. That lemma then substitutes the Chevalley hypothesis, while this file does not. The `hβγ`/`hγα` side proofs are duplicated too. (3) The calc tail, which turns `q·(p+1)·B_β` into `(p+1)²·B_γ` using the root-length ratio, is the same computation as the tail of `structureConstant_sq_eq_natCast_sq_of_killingForm_ratio`: push_cast; ring, then rw the ratio, then ring. The result is a 25-line calc of tiny ring steps that duplicates Normalization's argument.

Proposed change:

Add shared helpers in Symmetry.lean or Basic.lean:
(a) `killingForm_root_neg_ne_zero (hx) (γ) (hγ : γ.IsNonZero) : killingForm K L (x γ) (x (-γ)) ≠ 0`.
(b) `structureConstant_neg_neg_mul_killingForm_eq_neg (hx) α β γ hβ hγ hαβ : N(-α,-β,-γ) * B(x γ, x(-γ)) = -N(-α,γ,β) * B(x β, x(-β))`. This is hcyc followed by hskew.
(c) `chain_mul_killingForm_eq_sq (hlength : (q:K) * B_β = (p+1:ℕ) * B_γ) : ((q*(p+1) : ℕ) : K) * B_β = ((p+1:ℕ):K)^2 * B_γ`.
Then `structureConstant_neg_add_mul_killingForm_eq` is (b) plus `structureConstant_neg_neg_of_hom`. `structureConstant_sq_eq_natCast_sq_of_killingForm_ratio` uses (a) and (c). The main theorem here becomes: cancel with (a), rewrite with (b), rewrite with `hprod`, then close with (c) and `ring`. That is roughly 8 lines instead of 30, and the three argument pieces live in one place.

Benefit: Removes the duplicated cyclic/skew rewrite, the duplicated nonvanishing proof and the duplicated ratio arithmetic. The Chevalley and non-Chevalley variants then visibly differ only in how N(-α,-β) is handled. Future results on the same root string, such as integrality of constants, will not need to copy these steps again.

Source evidence:

- `TauCeti.IsSl2System.structureConstant_neg_add_mul_killingForm_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean`: have hcyclic := hx.structureConstant_mul_killingForm_eq γ (-α) β hβ hγα hγ
  have hskew := hx.structureConstant_skew (-α) γ β hβ hαγ
- `TauCeti.IsSl2System.structureConstant_sq_eq_natCast_sq_of_killingForm_ratio` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean`: have hkill : killingForm K L (x γ) (x (-γ)) ≠ 0 :=
    killingForm_ne_zero_of_mem_rootSpace hγ (hx.mem_rootSpace γ) (hx.ne_zero γ hγ)
      (hx.mem_rootSpace (-γ)) (hx.ne_zero (-γ) hγ.neg)
- `TauCeti.IsSl2System.structureConstant_sq_eq_natCast_sq_of_killingForm_ratio` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Normalization.lean`: ((chainBotCoeff α β + 1 : ℕ) : K) *
        ((chainTopCoeff α β : K) * killingForm K L (x β) (x (-β))) := by
          push_cast
          ring

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

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L372-L398)

Declaration: `pv_cutoff_F_integrable_delta_1 / pv_cutoff_F_integrable_1_2 / pv_cutoff_F_integrable_2_3delta vs pv_cutoff_integral_seg1_eq_inv / pv_cutoff_integral_seg2_eq_Ialpha / pv_cutoff_integral_seg3_eq_neg_inv`

The cutoff integrand F is computed on each open segment twice. Three integrability lemmas (lines 342–441) and three integral lemmas (lines 493–574) each re-prove the same pointwise fact. For example, `F t = I * ↑α` on Ioo 1 2 is proved at 380–390 and again at 526–536, in near-identical text. The seg1 version appears at 358–363 and 504–513, and the seg3 version at 412–425 and 557–570. Each copy repeats the same steps: unfold F, `ite_eq_left`, rewrite with the segment formula and derivative, `field_simp`, then bound the norm against ε. After that, each lemma repeats the same a.e. transfer from Ioo to Ioc, once for integrability (`Integrable.congr`, `Ioo_ae_eq_Ioc`) and once for the integral (`integral_congr_ae`, `eventuallyEqSet_iff`). Each pointwise block is about 10 lines, and there are three such blocks, each duplicated.

Proposed change:

Introduce the cutoff integrand once as a private def `pvCutoff r α ε t`. Then prove three pointwise lemmas. `pvCutoff_seg1 : δ = ε/r → δ < t → t < 1 → pvCutoff r α ε t = ↑(t⁻¹)`. `pvCutoff_seg2 : 0 < r → ε < r → t ∈ Ioo 1 2 → pvCutoff r α ε t = I * ↑α`. `pvCutoff_seg3 : ... t ∈ Ioo 2 (3-δ) → pvCutoff r α ε t = -↑((3-t)⁻¹)`. Add a generic helper `intervalIntegral_congr_Ioo {f g : ℝ → ℂ} {a b} (hab : a ≤ b) (h : ∀ t ∈ Ioo a b, f t = g t) : ∫ t in a..b, f t = ∫ t in a..b, g t`. Add a companion `IntervalIntegrable.congr_Ioo` that transfers IntervalIntegrable the same way. Each of the six lemmas then reduces to the pointwise lemma plus one helper call, and the repeated `Ioo_ae_eq_Ioc` boilerplate disappears. Adding `pvCutoff_eq_zero_of_norm_le` would also cover the zero pieces at 307–340 and 593–610.

Benefit: This removes roughly 80 lines of duplicated case analysis and a.e. plumbing. Each segment formula is then stated and proved once, which makes `pv_sector_cutoff_eq` easier to audit. The free-standing Ioo-to-Ioc congruence helpers are reusable in other PV computations.

Source evidence:

- `pv_cutoff_integral_seg2_eq_Ialpha` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`:   have h_on_Ioo : ∀ t ∈ Ioo 1 2, F t = I * ↑α := by
    intro t ⟨ht1, ht2⟩
    dsimp only [F]; simp only [sub_zero]; rw [ite_eq_left]
- `pv_cutoff_integral_seg3_eq_neg_inv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`:   apply intervalIntegral.integral_congr_ae
  filter_upwards [(Filter.eventuallyEqSet_iff.mp Ioo_ae_eq_Ioc)] with t ht
- `pv_cutoff_F_integrable_delta_1` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`:   rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]; exact h_F_Ioo

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L291-L297)

Declaration: `log_cancellation (duplicating integral_seg3_eq_log / integral_seg1_eq_neg_log)`

`log_cancellation` re-proves the substitution argument already established by `integral_seg3_eq_log` (lines 259–268). Both use `integral_neg`, then `integral_comp_sub_left` with `a := 2, b := 3 - _`, then `congr 1 <;> ring`, then `simp_all`. They differ only in that the endpoint is `ε` rather than `ε / r`. The same applies to h1 (lines 288–290) and `integral_seg1_eq_neg_log` (lines 254–257). The existing lemmas are never used, and `log_cancellation` reproduces them under the name `ε / r`. The `hε1` hypothesis of both lemmas is unused, so they are only stated for ε < 1 and could not be applied directly. That is why the proof was copied.

Proposed change:

Generalize `integral_seg3_eq_log` to `(δ) (hδ : 0 < δ)` (the `_hε1` hypothesis is unused) and likewise `integral_seg1_eq_neg_log`. Then derive `h1` and `h2` in `log_cancellation` by instantiating them at δ = ε / r. The proof of `log_cancellation` then reduces to the two instantiations, the `integral_ofReal` casts and `neg_add_cancel`. Alternatively, delete the unused `integral_seg*` lemmas and keep one copy.

Benefit: This removes a duplicated ~10-line substitution proof and makes the unused lemmas actually used. It also leaves one copy of the logarithmic-divergence calculation to maintain.

Source evidence:

- `integral_seg3_eq_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`:     have := intervalIntegral.integral_comp_sub_left (fun u => u⁻¹) (3 : ℝ)
      (a := (2 : ℝ)) (b := 3 - ε)
- `integral_seg1_eq_neg_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`:     ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε := by

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L307-L340)

Declaration: `pv_cutoff_F_integrable_0_delta / pv_cutoff_F_integrable_3delta_3 / hI1 / hI5 in pv_sector_cutoff_eq`

The fact that F vanishes where the curve is within ε of 0 (t ∈ [0,δ] on segment 1, and t ∈ [3-δ,3] on segment 3) is proved four times. It appears in the two integrability lemmas (307–340) and again inside `hI1` and `hI5` (593–610). Each copy repeats the same steps. It unfolds F, applies `ite_eq_right (not_lt.mpr _)`, rewrites with `sectorCurve_norm_seg1` or `sectorCurve_norm_seg3'`, and closes with `δ * r = ε` via `field_simp`. The integrability statements and the integral-equals-zero statements both follow from the pointwise vanishing.

Proposed change:

Prove two pointwise lemmas once: `pvCutoff_eq_zero_seg1 : t ∈ Icc 0 δ → F t = 0` and `pvCutoff_eq_zero_seg3 : t ∈ Icc (3-δ) 3 → F t = 0`. Alternatively, prove a single lemma `F t = 0` under `‖sectorCurve r α t‖ ≤ ε`. Then `integral_congr` + `integral_zero` gives hI1 and hI5. `intervalIntegrable_const.congr` gives the integrability results.

Benefit: This replaces four copies of a ~6-line argument with two short lemmas, and removes the duplicated `δ * r = ε` bookkeeping.

Source evidence:

- `pv_sector_cutoff_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`:       rw [sectorCurve_norm_seg3' r hr α t ⟨by linarith [ht.1], ht.2⟩]
      calc (3 - t) * r ≤ δ * r := by nlinarith [ht.1]
- `pv_cutoff_F_integrable_3delta_3` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`:   rw [sectorCurve_norm_seg3' r hr α t ⟨h2, ht.2⟩]
  have : (3 - t) * r ≤ δ * r := mul_le_mul_of_nonneg_right (by linarith [ht.1]) hr.le

### repeated-proof-machinery: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L328-L428)

Declaration: `norm_poitouVerticalProfileDerivative_regularized_le / norm_poitouVerticalProfileSecondDerivative_regularized_le`

The first- and second-derivative decay bounds repeat one long argument. Both prove the phase bound exp((σ-1/2)x) ≤ exp(a|x|) (hphase). Both unfold the norm of the complex sum with the same `simp only [norm_mul, Complex.norm_real, ..., Complex.norm_exp ...]; norm_num; hnorm : ‖(σ:ℂ)-1/2‖ = a` block. Both bound the pieces by polynomial × exp(-δx²) × exp(a|x|). Both finish by rewriting with Real.exp_add and applying exp_neg_mul_sq_add_mul_le to reach exp(a²/(2δ))·exp(-(δ/2)x²). The second proof (about 190 lines) re-types the large polynomial P several times, once per sub-calc.

Proposed change:

Add two small helpers before both theorems. (1) `norm_ofReal_mul_exp_sub_half_le`: for real u, σ, x, ‖(u:ℂ) * Complex.exp ((σ-1/2)*x)‖ = |u| * Real.exp ((σ-1/2)*x) (and the version with the extra factor (σ-1/2)), which replaces the repeated simp/hnorm block. (2) `gaussian_phase_absorb`: for hδ : 0 < δ, 0 ≤ P and a ≥ 0, P * Real.exp (-δ*x^2) * Real.exp (a*|x|) ≤ Real.exp (a^2/(2*δ)) * (P * Real.exp (-(δ/2)*x^2)). Its proof is `exp_add` plus `exp_neg_mul_sq_add_mul_le`. Also state `exp_sub_half_mul_le : Real.exp ((σ-1/2)*x) ≤ Real.exp (|σ-1/2|*|x|)`. Each norm theorem would then reduce to: triangle inequality, `mul_le_mul` against hk/hk'/hk'' and the phase bound, then one application of the absorb lemma with an explicit polynomial P (named once with `set`). This would remove the duplicated hP nonnegativity proofs and the restated polynomial in the second theorem.

Benefit: Cuts roughly 60–100 lines and states the real analytic content once: Gaussian decay beats the exponential phase factor. The same helpers would serve any higher-derivative bound, so a third derivative becomes a short proof instead of another copy.

Source evidence:

- `norm_poitouVerticalProfileSecondDerivative_regularized_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: _ ≤ _ := mul_le_mul_of_nonneg_left
          (exp_neg_mul_sq_add_mul_le hδ a x) hP
- `norm_poitouVerticalProfileDerivative_regularized_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: have hphase :
      Real.exp ((σ - 1 / 2) * x) ≤
        Real.exp (a * |x|) := by
- `exp_neg_mul_sq_add_mul_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedTartarTransform.lean`: exp_neg_mul_sq_add_mul_le hδ |s.re - 1 / 2| x

### repeated-proof-machinery: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L556-L580)

Declaration: `fourier_poitouVerticalProfileDerivative_regularized / fourier_poitouVerticalProfileSecondDerivative_regularized`

The two theorems have the same proof. Each rewrites `deriv g = g'` by funext, applies `Real.fourier_deriv` with integrability, differentiability and integrability of the derivative, and closes with `simp_all`. They differ only in the function g and its derivative g'. The same `Real.fourier_deriv` + `congrFun` + `simp_all` scaffold also appears elsewhere in the repository, in MooreBound/PrimeNumberTheoremAnd/Fourier.lean line 125.

Proposed change:

Add a general lemma, for example `fourier_eq_smul_fourier_of_hasDerivAt {g g' : ℝ → ℂ} (hg : Integrable g) (hd : ∀ x, HasDerivAt g (g' x) x) (hg' : Integrable g') (w : ℝ) : 𝓕 g' w = (2 * π * I * w) • 𝓕 g w`. Its proof builds `deriv g = g'` from `(hd x).deriv` and differentiability from `(hd x).differentiableAt`, then runs the existing `Real.fourier_deriv` argument once. Both theorems become one-liners that pass `hasDerivAt_poitouVerticalProfile ...` or `hasDerivAt_regularizedPoitouVerticalProfileDerivative ...`. The auxiliary `deriv_…` and `differentiable_…` lemmas at 538–553 and 895–915 would then be unnecessary except where used elsewhere. In particular, `aestronglyMeasurable_deriv` at 1138 could use `Continuous`/measurability from HasDerivAt instead.

Benefit: Removes about 40 duplicated lines. A reusable lemma, 'Fourier transform of a HasDerivAt-derivative', replaces the repeated `deriv` bookkeeping, and the two Fourier statements no longer need their own hderiv/funext blocks.

Source evidence:

- `fourier_poitouVerticalProfileSecondDerivative_regularized` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`:     congrFun (Real.fourier_deriv
      (poitouVerticalProfileDerivative_regularized_integrable hδ y σ)
- `(anonymous lemma using Real.fourier_deriv)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MooreBound/PrimeNumberTheoremAnd/Fourier.lean`: have h := congrFun (Real.fourier_deriv hg hdiff hg') w

### repeated-proof-machinery: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L430-L449)

Declaration: `poitouVerticalProfileDerivative_regularized_integrable / integrable_quadratic_abs_mul_exp_neg_mul_sq`

The proof of integrability of the first-derivative majorant (hzero/hone) rebuilds a special case of `integrable_quadratic_abs_mul_exp_neg_mul_sq`, which is proved later at 918. That lemma gives integrability of (A + B|x| + C x²)·exp(-b x²), and the same `integrable_exp_neg_mul_sq` / `integrable_mul_exp_neg_mul_sq ... .norm` / `simp_all` steps appear in both places. The first theorem uses the specific form K*(A*e) + K*((2δ)*(|x|*e)), which is the case C = 0, scaled by K.

Proposed change:

Move `integrable_quadratic_abs_mul_exp_neg_mul_sq` above poitouVerticalProfileDerivative_regularized_integrable. Use `((integrable_quadratic_abs_mul_exp_neg_mul_sq (half_pos hδ) A (2*δ) 0).const_mul K).mono'` and let `norm_poitouVerticalProfileDerivative_regularized_le` end with `trans_eq` and `grind`/`ring`, as the second-derivative proof already does with `hmajor`. This deletes hzero/hone and the manual `hzero.add hone`.

Benefit: Both integrability proofs then share the one Gaussian-moment lemma, and a reader sees that the first and second derivative cases differ only in the polynomial degree.

Source evidence:

- `integrable_quadratic_abs_mul_exp_neg_mul_sq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: have h := (integrable_mul_exp_neg_mul_sq hb).norm.const_mul B
- `poitouVerticalProfileSecondDerivative_regularized_integrable` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: (integrable_quadratic_abs_mul_exp_neg_mul_sq
      (half_pos hδ) A B C).const_mul E

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138-L160)

Declaration: `positiveShell_pairwise`

The proof that dyadic shells with different indices are disjoint is written out from scratch four times. It appears here for ℕ indices, in Kernel.lean for `{k : ℤ // k < 0}` (`pairwise_disjoint_parabolicRieszShells`), in Kernel.lean for `negativeShell`, and in Adams.lean for `nearShell` (`nearShell_pairwise`). Each copy runs the same steps: `rcases lt_or_gt_of_ne`, an index inequality `k+1 ≤ l`, `Real.rpow_le_rpow_of_exponent_le`, `mul_le_mul_of_nonneg_right ... hR.le`, `not_lt_of_ge`. Each copy then repeats the whole block with the roles of the two indices swapped. The only mathematical fact used is that shells `parabolicRieszShell R k z` and `parabolicRieszShell R l z` are disjoint whenever `k < l`. That fact is never stated for integer indices, so each caller rebuilds it.

Proposed change:

In Kernel.lean, next to `parabolicRieszShell`, add one lemma `parabolicRieszShell_disjoint_of_lt {R} (hR : 0 < R) {k l : ℤ} (hkl : k < l) (z) : Disjoint (parabolicRieszShell R k z) (parabolicRieszShell R l z)`. Prove it once: `2^(k+1) R ≤ 2^l R ≤ ρ`, which contradicts `ρ < 2^(k+1) R`. Derive the symmetric case with `Disjoint.symm`, so a `lt_or_gt_of_ne` split yields `parabolicRieszShell_disjoint_of_ne` in one line. Then `positiveShell_pairwise` becomes `fun n m h => parabolicRieszShell_disjoint_of_ne hR (by exact_mod_cast h) z`. The Kernel and Adams versions use the same lemma, with `Int.negSucc` injectivity or `Subtype` coercion for the index map.

Benefit: This replaces roughly 4 × 20 lines with one ~12-line lemma and four one-line uses. It also removes the duplicated mirror-image branches, and later shell decompositions can reuse the lemma.

Source evidence:

- `negativeShell_pairwise` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`:     have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwn.1)) hwm.2
- `nearShell_pairwise` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Adams.lean`:     have hrad := mul_le_mul_of_nonneg_right hpow hR.le
    exact (not_lt_of_ge (hrad.trans hwn.1)) hwm.2
- `pairwise_disjoint_parabolicRieszShells` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`:       apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L93-L128)

Declaration: `exists_positive_shell`

`exists_positive_shell` and `exists_shell_of_pos_lt` (Kernel.lean) share about 25 lines of identical machinery. Both take `x = ρ/R` and `k = ⌊log x / log 2⌋`. Both derive `2^k ≤ x < 2^(k+1)` through `Real.strictMonoOn_log`, `Real.log_rpow` and `field_simp`. Both convert this to `2^k R ≤ ρ < 2^(k+1) R` and apply `mem_parabolicRieszShell`. They differ only in the sign check on `k`: `0 ≤ k` here, `k < 0` there. The general fact is that every point with `ρ > 0` lies in some shell with an integer index. No lemma states this, so it is proved twice with sign handling mixed in.

Proposed change:

Add one lemma in Kernel.lean, `exists_int_shell {z w} {R} (hR : 0 < R) (hρ : 0 < parabolicRho₂ z w) : ∃ k : ℤ, (2:ℝ)^(k:ℝ) * R ≤ parabolicRho₂ z w ∧ parabolicRho₂ z w < (2:ℝ)^((k:ℝ)+1) * R`. A form that also carries `k = ⌊log x / log 2⌋`, or the facts `1 ≤ x → 0 ≤ k` and `x < 1 → k < 0`, would also work. Alternatively, derive the sign bounds from the shell membership: `1 ≤ ρ/R` together with `ρ < 2^(k+1) R` forces `0 ≤ k` by monotonicity of `2^·`. Then `exists_positive_shell` reduces to this lemma plus the sign argument and `Int.toNat`. `exists_shell_of_pos_lt` likewise reduces to this lemma plus a sign argument.

Benefit: This removes about 25 duplicated lines of floor/log bookkeeping. It states the natural covering fact `⋃ k : ℤ, shell R k z ⊇ {ρ > 0}` once, and the near-field and far-field decompositions then differ only in a short sign argument.

Source evidence:

- `exists_shell_of_pos_lt` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`:   let k : ℤ := ⌊Real.log x / L⌋
  have hL : 0 < L := Real.log_pos (by norm_num)
- `exists_shell_of_pos_lt` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`:       _ < ((k : ℝ) + 1) * L := mul_lt_mul_of_pos_right hkhi hL

### repeated-proof-machinery: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L82-L96)

Declaration: `RS.dslope_const_mul / RS.dslope_const (with RS.dslope_sub_mul and Filter.EventuallyEq.dslope_eq)`

Four pointwise dslope lemmas (EventuallyEq.dslope_eq at lines 65-72, dslope_const_mul, dslope_const, dslope_sub_mul at 156-167) repeat the same skeleton. Each does `funext b` (or filter_upwards), then `rcases eq_or_ne b z₀`. The diagonal branch is closed by `dslope_same` plus a derivative fact. The off-diagonal branch rewrites `dslope_of_ne _ hbz` twice and `slope_def_field` twice before closing with `ring` or `simp`. The case split and the two-sided rewriting are re-derived each time.

Proposed change:

Add one helper that reduces equality of two dslopes to a derivative equality plus a pointwise slope equality: `theorem dslope_congr_of_slope {f g : ℂ → ℂ} {z₀} (hd : deriv f z₀ = deriv g z₀) (hs : ∀ b, b ≠ z₀ → slope f z₀ b = slope g z₀ b) : dslope f z₀ = dslope g z₀`. A pointwise version, `∀ b, dslope f z₀ b = dslope g z₀ b` under the same hypotheses, would also serve EventuallyEq.dslope_eq. Then `dslope_const_mul` becomes `dslope_congr_of_slope (by simp [deriv_const_mul_field]) (fun b hb => by simp only [slope_def_field]; ring)`. `dslope_const` becomes the same call with `hd` by `simp` and `hs` by `simp [slope_def_field]`. The same shape works for EventuallyEq.dslope_eq. `dslope_sub_mul` can use it too if its left side is first rewritten with `dslope_sub_smul_of_ne`.

Benefit: The `funext`/`rcases`/double-`dslope_of_ne` boilerplate is stated once. Each use then only supplies the two mathematical facts: the derivative agrees, and the slopes agree off the diagonal. That makes the proofs shorter and easier to follow.

Source evidence:

- `RS.dslope_const` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`:   · rw [dslope_of_ne _ hbz, slope_def_field]
- `Filter.EventuallyEq.dslope_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`:   · rw [dslope_of_ne _ hbz, dslope_of_ne _ hbz, slope_def_field, slope_def_field, hb, hz]
- `ContinuousLinearMap.dslope_comp` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/DSlope.lean`: rcases eq_or_ne b a with (rfl | hne)

### repeated-proof-machinery: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L97-L103)

Declaration: `RS.taylorCoeffAt_const_mul / RS.taylorCoeffAt_zero_fun / RS.taylorCoeffAt_congr / RS.taylorCoeffAt_sub_pow_mul`

Several results use the same induction on `j`. They unfold `taylorCoeffAt_succ`, rewrite once with a dslope-commutation lemma, and close with the induction hypothesis. This happens in taylorCoeffAt_congr (74-80), taylorCoeffAt_const_mul (97-103), taylorCoeffAt_zero_fun (105-108), taylorCoeffAt_const (110-114) and taylorCoeffAt_sub_pow_mul (170-188). In each case the real content is a statement about how `dslope` transforms the function. The induction over iterates is routine bookkeeping that is repeated.

Proposed change:

Add one transfer lemma stating that Taylor coefficients follow any operation that dslope intertwines. Sketch: for `T : (ℂ → ℂ) → (ℂ → ℂ)` and a coefficient map `φ : ℂ → ℂ` with `(∀ g, (T g) z₀ = φ (g z₀))` and `(∀ g, dslope (T g) z₀ = T (dslope g z₀))`, we get `∀ g j, taylorCoeffAt (T g) z₀ j = φ (taylorCoeffAt g z₀ j)`. Its proof is one induction, generalizing `g`, using `taylorCoeffAt_succ`. Then `taylorCoeffAt_const_mul` is the instance `T g = fun z => c * g z`, `φ = (c * ·)`, with `dslope_const_mul` as the intertwining fact. `taylorCoeffAt_neg` is the instance `c = -1`. A companion lemma for the dslope-kills-constants case would handle `taylorCoeffAt_zero_fun` and `taylorCoeffAt_const`. `taylorCoeffAt_congr` could share the same induction scaffold in a version with a relation `R` in place of equality.

Benefit: The per-lemma `induction j generalizing g` blocks are replaced by a single reusable induction. New linear operations on germs, such as scalar multiplication or conjugation-type maps, would then only need a one-line dslope commutation lemma. The file would also say explicitly that Taylor coefficients are equivariant for operations that commute with dslope.

Source evidence:

- `RS.taylorCoeffAt_zero_fun` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`:   | succ j ih => rw [taylorCoeffAt_succ, dslope_const]; exact ih
- `Filter.EventuallyEq.dslope_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`:     exact ih (Filter.EventuallyEq.dslope_eq hfg)
- `RS.taylorCoeffAt_sub_pow_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`:       rw [hfun, taylorCoeffAt_succ, dslope_sub_mul hdiff, ih j]

### repeated-proof-machinery: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L188-L226)

Declaration: `weakPathRepresentative_pairing_eq_inner / FrozenDriftProblem.initial_pairing_eq_cell_integral`

The two theorems repeat one argument. Each fixes ψT := smoothPeriodicTestL2 hψ hperiodic and gets `ψT =ᵐ periodicToTorus ψ` from `coeFn_toLp`. Each then runs the same chain: `L2.inner_def`, then `integral_congr_ae` with `simp [mul_comm]`, then `integral_congr_ae` with a `show periodicToTorus (fun y => g y * ψ y) x = periodicToTorus g x * periodicToTorus ψ x from rfl` rewrite, then `integral_periodicToTorus_eq_unitCell`, then `integral_unitCell_eq_unitCube`. This is about 25 lines of non-trivial proof in each theorem. Only the periodic function g differs: it is `weakPathRepresentative u t` in one and `P.θ₀` in the other. The facts used about the torus class (`htheta` in one, `hθ` in the other) are both of the form `f =ᵐ periodicToTorus g`.

Proposed change:

Add one helper before these theorems: `theorem inner_smoothPeriodicTestL2_eq_cell_integral (f : ScalarTorusL2) (g : Vec 2 → ℝ) (hfg : (fun x : Torus => f x) =ᵐ[volume] AVenhance.Infra.Torus.periodicToTorus g) {ψ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hperiodic : AVenhance.IsZ2Periodic ψ) : inner ℝ f (smoothPeriodicTestL2 hψ hperiodic) = ∫ x in AVenhance.unitCube, g x * ψ x`. Prove it with the existing calc chain, using `hfg` and `hψT` in the pointwise step. Then `weakPathRepresentative_pairing_eq_inner` follows from `(helper (u t) _ (Filter.Eventually.of_forall htheta) hψ hperiodic).symm`, keeping only `htheta`. `FrozenDriftProblem.initial_pairing_eq_cell_integral` follows from `helper P.initialTorusL2 P.θ₀ hθ hψ hperiodic`, keeping only `hθ`. If a pointwise version is also wanted, `htheta` can be fed through `Filter.Eventually.of_forall`.

Benefit: This removes about 30 duplicated lines. The statement 'a torus class that is a.e. the periodization of g pairs with a smooth periodic test as ∫ over the unit cube of g·ψ' is the natural bridge between torus Hilbert pairings and Euclidean cell integrals. Later weak-solution assembly can reuse it directly. The two theorems become short corollaries, and any change to the torus measure conventions has to be fixed in one place only.

Source evidence:

- `FrozenDriftProblem.initial_pairing_eq_cell_integral` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: AVenhance.Infra.Torus.periodicToTorus P.θ₀ x *
            AVenhance.Infra.Torus.periodicToTorus ψ x from rfl,
- `integral_periodicToTorus_eq_unitCell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: ∫ x : UnitAddTorus (Fin d), periodicToTorus f x = ∫ x in unitCell d, f x

### repeated-proof-machinery: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L168-L184)

Declaration: `weakPathRepresentative_memL2On / weakPathRepresentative_l2NormSq / weakPathRepresentative_pairing_eq_inner`

The same unfolding fact is re-proved four times. It is `weakPathRepresentative u t = scalarTorusRepresentative (u ⟨t, ht⟩)` for `t ∈ Icc 0 1`. It appears as `hfun` in `_isPeriodic` (the in-interval branch), `hfun` in `_memL2On`, `hfun` in `_l2NormSq`, and `hrep` inside `_pairing_eq_inner`. Each copy does `funext` and then `simp [weakPathRepresentative, …]`. The `_memL2On` and `_l2NormSq` theorems each consist only of this step followed by `rw` and the corresponding `scalarTorusRepresentative_*` lemma.

Proposed change:

Add `theorem weakPathRepresentative_of_mem (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (t : Icc (0 : ℝ) 1) : weakPathRepresentative u t = scalarTorusRepresentative (u t)`, proved once by `funext x; simp [weakPathRepresentative, t.property]`. Then `_memL2On` becomes `(weakPathRepresentative_of_mem u t) ▸ scalarTorusRepresentative_memL2On (u t)`, or `rw [weakPathRepresentative_of_mem]; exact …`. `_l2NormSq` is the same. `htheta` in `_pairing_eq_inner` uses `rw [weakPathRepresentative_of_mem]`. The in-interval branch of `_isPeriodic` uses it with `⟨t, ht⟩`. A similar `weakPathRepresentative_of_not_mem` for the zero branch is optional.

Benefit: The definition's case split is unfolded in one place and the downstream proofs are one-line rewrites. If `weakPathRepresentative` changes (for example, a different value outside the interval), only the helper needs updating. The statement is a natural simp-style characterisation lemma, and it gives an obvious `@[simp]` candidate.

Source evidence:

- `weakPathRepresentative_l2NormSq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`:   have hfun : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by
- `weakPathRepresentative_pairing_eq_inner` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`:     have hrep : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by

### repeated-proof-machinery: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L54-L110)

Declaration: `planeCurveToBivariate_X_zero / planeCurveToBivariate_X_one / planeCurveToBivariate_C / planeCurveToBivariate_natDegree_eq_degreeOf_zero`

Four lemmas about `planeCurveToBivariate` each unfold the definition with `rw [planeCurveToBivariate]` and then restate the goal with an explicit `change Polynomial.map (uniqueAlgEquiv K (Fin 1)).toRingHom (finSuccEquiv K 1 _)`. Three of them (`X_zero`, `X_one`, `C`) then repeat the same pattern: prove an inner `finSuccEquiv` identity `hinner`, rewrite with it, and finish with `simp`. The `change` blocks are long and fragile, and they reproduce the definition body in each place. No lemma states `planeCurveToBivariate K f = (finSuccEquiv K 1 f).map (uniqueAlgEquiv K (Fin 1)).toRingHom`, so every proof redoes it.

Proposed change:

Add one unfolding lemma, `planeCurveToBivariate_apply (f) : planeCurveToBivariate K f = Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom (MvPolynomial.finSuccEquiv K 1 f) := rfl`. Each of the four lemmas then starts with `rw [planeCurveToBivariate_apply]`. The `change` blocks go away. The three simp lemmas keep only their `hinner` computation and a closing `simp`. The `natDegree` lemma becomes `rw [planeCurveToBivariate_apply, Polynomial.natDegree_map_eq_of_injective ...]; exact MvPolynomial.natDegree_finSuccEquiv f`.

Benefit: This removes four copies of the definition-restating `change`, about 12 lines in all. It gives one named, reusable unfolding statement and makes the proofs robust to changes in how `planeCurveToBivariate` is defined.

Source evidence:

- `planeCurveToBivariate_natDegree_eq_degreeOf_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: ((MvPolynomial.finSuccEquiv K 1 f).map
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom).natDegree = _
- `planeCurveToBivariate_C` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C c)) =
      Polynomial.C (Polynomial.C c)

### repeated-proof-machinery: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L436-L554)

Declaration: `planeCurve_auxiliaryFamily_linearIndependent_of_nonzero_partials / ..._of_absoluteIrreducible / ..._of_absoluteIrreducible_coordinateDegrees (and the main theorem)`

The same instance-setup block appears in four theorems: the main theorem and the `_of_nonzero_partials`, `_of_absoluteIrreducible` and `_coordinateDegrees` variants. The block has three parts: `IsDomain (PlaneCurveCoordinateRing f)`, `CharP (PlaneCurveFunctionField f) p`, and, in the last two, the derivation of `Irreducible f` from absolute irreducibility. In the last two theorems it is written out twice each, once in the `let`/`letI` header of the statement and once in the proof body. The `Irreducible f` derivation is exactly `irreducible_of_irreducible_map_algebraicClosure` in `PlaneCurveBidegreeBridge.lean`. Re-deriving it costs four copies of the `simpa only [MvPolynomial.map_id] using ...` block, 2 in statements and 2 in proofs. The `CharP` instance for the function field is likewise rebuilt from `charP_of_injective_algebraMap` in each of the four theorems.

Proposed change:

Reuse the existing `irreducible_of_irreducible_map_algebraicClosure habsolute` by importing `PlaneCurveBidegreeBridge`. Its imports are a subset of this file's, plus `External.GeneralCurveTheorems`. Alternatively, move that lemma into `AbsoluteIrreducibilityBaseChange`, which the target already imports. Then replace the `let hf : Irreducible f := by simpa ...` header and body blocks with `irreducible_of_irreducible_map_algebraicClosure habsolute`. Also add a small lemma or instance, such as `planeCurveFunctionField_charP (hf : Irreducible f) : CharP (PlaneCurveFunctionField f) p`, stating the injective-algebraMap argument once. The statements and proofs would then use it instead of re-inlining the `charP_of_injective_algebraMap` block.

Benefit: This removes about 20 lines of duplicated setup across the four theorems. It also removes the duplicated derivation of `Irreducible f`, because an existing lemma already proves it. The statements become easier to read, and the instance construction lives in one place.

Source evidence:

- `irreducible_of_irreducible_map_algebraicClosure` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveBidegreeBridge.lean`: have h := irreducible_map_of_irreducible_map_algebraicClosure
    (RingHom.id K) f habsolute
  rw [MvPolynomial.map_id] at h
  exact h
- `planeCurve_auxiliaryFamily_linearIndependent` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: let : CharP (PlaneCurveFunctionField f) p :=
    charP_of_injective_algebraMap
      (algebraMap K (PlaneCurveFunctionField f)).injective p

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

### readable-proof-simplification: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L93-L93)

Declaration: `tendsto_rpow_atBot_of_base_gt_one`

The goal `0 < log b` is closed by going through `log_pos_iff`, which needs a side goal `0 ≤ b` discharged by `positivity`, and then an opaque `aesop` call for `1 < b`. The hypothesis `hb : 1 < b` is already in context, and `Real.log_pos` states exactly this implication. The sibling lemma `tendsto_rpow_atTop_of_base_gt_one` (line 87) uses `log_pos hb` for the same goal.

Proposed change:

Replace line 93 with `exact log_pos hb`.

Benefit: It removes two automation calls (`positivity` and `aesop`) and one needless iff, so the reader sees directly that `1 < b` gives `0 < log b`. It also makes this lemma match the proof of `tendsto_rpow_atTop_of_base_gt_one`, and it is faster and less fragile than `aesop`.

Source evidence:

- `Real.log_pos` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`: theorem log_pos (hx : 1 < x) : 0 < log x :=
- `tendsto_rpow_atTop_of_base_gt_one` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: exact log_pos hb

### readable-proof-simplification: [Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean#L98-L103)

Declaration: `CategoryTheory.Functor.IsWellOrderContinuous.restriction_setIci`

The `j' ≤ j` branch has to show that `⟨j, _⟩ < m` in `Set.Ici j`. It does this with a five-line tactic sequence: `by_contra`, a `simp only` to normalise the hypothesis, `apply hm.1`, a `rintro` that destructs the subtype, and a final `exact`. The `simp only [Set.mem_Iio, not_lt]` and the destructuring of `⟨k, hk⟩` only unfold definitions. The `hkm` hypothesis is never used. The mathematical idea is simply that `⟨j, _⟩` is the minimum of `Set.Ici j`, so `m ≤ ⟨j, _⟩` would make `m` minimal, contradicting that `m` is a limit element. The tactic bookkeeping hides this. The same branch also uses `le_refl j` where `le_rfl` is enough.

Proposed change:

Replace the block with a term-mode proof of the same argument:
```lean
      · refine ⟨⟨⟨j, le_rfl⟩, ?_⟩, h⟩
        show _ < m
        exact lt_of_not_ge fun h' ↦ hm.1 fun k _ ↦ h'.trans k.2
```
Here `h' : m ≤ ⟨j, _⟩`, and `k.2 : j ≤ k.1` gives `⟨j, _⟩ ≤ k`. So `h'.trans k.2 : m ≤ k` is exactly `IsMin m`. If the `show` line is not needed, it can be dropped. I have not compiled this.

Benefit: The proof reads as the intended argument: if `m` were at most the minimum of the interval, it would be minimal, which contradicts `hm.1`. It drops the `simp only` normalisation, the pattern-matching `rintro` and the unused `hkm`, so the branch is two lines.

Source evidence:

- `Set.not_isMin_coe` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SetIsMax.lean`: fun h ↦ hm (fun _ hb ↦ h hb)
- `Set.Ici.isSuccLimit_coe` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/Interval/Set/Limit.lean`: ⟨Set.not_isMin_coe _ hm.1, fun b ↦ by

### readable-proof-simplification: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L319-L323)

Declaration: `Bundle.Trivialization.mk_coordChangeL (and VectorPrebundle.mk_coordChange)`

The first component only needs `b = (e' ⟨b, e.symm b y⟩).1`. The proof rewrites `⟨b, e.symm b y⟩` into `e.toOpenPartialHomeomorph.symm (b, y)` with `mk_symm`, then repeats `proj_symm_apply'` in two separate `rw` blocks, and then closes a side goal. The projection of `⟨b, _⟩` is `b` by definition, so `coe_fst'` already gives the goal directly from `hb.2`. The same detour is copy-pasted in `VectorPrebundle.mk_coordChange`.

Proposed change:

Replace the first bullet by `· exact (e'.coe_fst' (x := ⟨b, e.symm b y⟩) hb.2).symm`, which does not use `mk_symm` or `proj_symm_apply'`. In `VectorPrebundle.mk_coordChange` use `(e'.coe_fst' (x := ⟨b, e.symm b v⟩) hb.2).symm` in the same way, since `Pretrivialization.coe_fst'` exists with the same shape. If unification struggles, add `show b = (e' ⟨b, e.symm b y⟩).1` first.

Benefit: The reader sees that the first coordinate is preserved because `b` lies in `e'.baseSet`. The current proof hides this behind rewrites into the partial homeomorphism, and the duplicated `rw` goes away in both places.

Source evidence:

- `Bundle.Trivialization.coe_fst'` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/FiberBundle/Trivialization.lean`: theorem coe_fst' (ex : proj x ∈ e.baseSet) : (e x).1 = proj x :=
- `VectorPrebundle.mk_coordChange` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`:   · rw [e.mk_symm hb.1 v, e'.coe_fst', e.proj_symm_apply' hb.1]
    rw [e.proj_symm_apply' hb.1]
    exact hb.2

### readable-proof-simplification: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L232-L234)

Declaration: `Bundle.Trivialization.coe_linearMapAt_of_mem`

The proof repeats the `simp_rw` proof of `Pretrivialization.coe_linearMapAt_of_mem`, which has the same statement. The neighbouring `Trivialization.coe_linearMapAt` already delegates to `e.toPretrivialization`, since `Trivialization.linearMapAt` is defined through the pretrivialization. This lemma does not follow that pattern.

Proposed change:

Replace the tactic block by the term `e.toPretrivialization.coe_linearMapAt_of_mem hb`. Keep the `@[simp]` attribute.

Benefit: The Trivialization lemma delegates to the Pretrivialization lemma, as `coe_linearMapAt` just above does. The `simp_rw` proof is no longer maintained in two places.

Source evidence:

- `Bundle.Pretrivialization.coe_linearMapAt_of_mem` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`:     (hb : b ∈ e.baseSet) : ⇑(e.linearMapAt R b) = fun y => (e ⟨b, y⟩).2 := by
  simp_rw [coe_linearMapAt, ite_eq_left hb]
- `Bundle.Trivialization.coe_linearMapAt` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`:   e.toPretrivialization.coe_linearMapAt b

### readable-proof-simplification: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L605-L607)

Declaration: `VectorBundleCore.coordChange_linear_comp`

The proof is a `by` block inside a `fun`, with unusual indentation, only to apply extensionality and then use a hypothesis that already has exactly the pointwise form needed.

Proposed change:

Write `fun x hx => ContinuousLinearMap.ext (Z.coordChange_comp i j k x hx)`. This should work because `(f.comp g) v` unfolds to `f (g v)` by definition.

Benefit: The statement becomes a one-line term showing that equality of the composite maps is the pointwise `coordChange_comp` field. It also removes the awkward `fun ... => by` layout.

Source evidence:

- `VectorBundleCore (structure field coordChange_comp)` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: (coordChange j k x) (coordChange i j x v) = coordChange i k x v

### readable-proof-simplification: [Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L126-L127)

Declaration: `CliffordAlgebra.contractLeft_ι_mul (same pattern in contractLeft_ι and contractLeft_algebraMap)`

The `exact` step eta-expands `contractLeftAux_contractLeftAux Q d` into `fun m x fx ↦ ... m x fx`. The binder-and-application wrapper only restates the lemma's own arguments. The same three lines recur in `contractLeft_ι` (line 159) and `contractLeft_algebraMap` (line 169). In the definition of `contractLeft` the same hypothesis is passed directly as `(contractLeftAux_contractLeftAux Q d)`.

Proposed change:

Keep the `refine` (which fixes the unification issue mentioned in the porting note) and drop the eta-expansion:
  refine foldr'_ι_mul _ _ ?_ _ _ _
  exact contractLeftAux_contractLeftAux Q d
Apply the same change at lines 159 and 169. The two forms are eta-equivalent, so the elaboration should be unchanged. The `(contractLeftAux_contractLeftAux Q d)` argument in the `contractLeft` definition is evidence that the partially applied lemma has the right type.

Benefit: The reader sees directly that the hypothesis of `foldr'_ι_mul` is the auxiliary lemma `contractLeftAux_contractLeftAux Q d`. They no longer have to check that the binders `m x fx` are just passed through. It is also consistent with how `contractLeft` is defined.

Source evidence:

- `CliffordAlgebra.contractLeft` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: toFun d := foldr' Q (contractLeftAux Q d) (contractLeftAux_contractLeftAux Q d) 0
- `CliffordAlgebra.foldr'_ι_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Fold.lean`: (hf : ∀ m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x) :

### readable-proof-simplification: [Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L332-L337)

Declaration: `CliffordAlgebra.changeFormEquiv`

`fun x => by exact <term>` is a tactic block wrapping a single term, so the `by exact` adds nothing. The parentheses in `(add_neg_cancel B)` and `(neg_add_cancel B)` are also redundant. The same applies to `right_inv`.

Proposed change:

    left_inv := fun x =>
      (changeForm_changeForm _ _ x).trans <|
        by simp_rw [add_neg_cancel B, changeForm_self_apply]
    right_inv := fun x =>
      (changeForm_changeForm _ _ x).trans <|
        by simp_rw [neg_add_cancel B, changeForm_self_apply]

Benefit: The two fields become plain terms that read as "compose `changeForm_changeForm`, then rewrite `B + -B = 0` and apply `changeForm_self_apply`". The argument is the same, minus the redundant `by exact` wrapper and parentheses. Elsewhere in the file the same `.trans <| by …` shape is already written as a bare term (e.g. `changeForm_ι` and `changeForm_ι_mul`).

Source evidence:

- `CliffordAlgebra.changeForm_ι_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: (foldr_mul _ _ _ _ _ _).trans <| by rw [foldr_ι]; rfl

### readable-proof-simplification: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L140-L143)

Declaration: `rootsOfUnityCircleEquiv_comp_rootsOfUnityAddChar_val`

The simp call rewrites right to left with `← ZMod.toCircle_natCast`. It also removes `ZMod.natCast_val` from the simp set, and then re-adds `natCast_zmod_val` to undo the cast. A reader has to simulate simp to see why the lemma is run backwards and why one simp lemma is excluded. The goal is a direct chain of three existing lemmas, each already stated in the matching coercion form: `rootsOfUnityCircleEquiv_apply` (rfl, simp), `ZMod.rootsOfUnityAddChar_val` (rfl, simp) and `ZMod.toCircle_apply`. The proof does not use that chain.

Proposed change:

Replace the proof with the explicit rewrite chain:
  rw [rootsOfUnityCircleEquiv_apply, ZMod.rootsOfUnityAddChar_val, ZMod.toCircle_apply]
The first step unfolds the equivalence to the circle coercion. The second replaces the root-of-unity character by `toCircle j`. The third applies the explicit formula `exp (2 * π * I * j.val / N)`. If a coercion fails to match syntactically, `exact ZMod.toCircle_apply j` after the first two rewrites should close the goal.

Benefit: The proof now follows the mathematical steps one by one. It no longer relies on a `←` rewrite, a removed simp lemma and a re-added cast lemma that cancel each other. It is also less fragile if the simp set around `ZMod.natCast_val` changes.

Source evidence:

- `rootsOfUnityCircleEquiv_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: ((rootsOfUnityCircleEquiv n w).val : ℂ) = ((w.val : Circle) : ℂ)
- `ZMod.rootsOfUnityAddChar_val` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: (rootsOfUnityAddChar n x).val = toCircle x
- `ZMod.toCircle_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: toCircle j = exp (2 * π * I * j.val / N)

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

### readable-proof-simplification: [TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LinearAlgebra/Matrix/SpecialOrthogonalGroup/Center.lean#L65-L66)

Declaration: `Matrix.mem_range_scalar_of_commute_specialOrthogonalGroup (hoff step)`

The last step of `hoff` manually cancels the regular element 2. It builds `2 * M i j = 2 * 0` by transitivity with a symmetric `mul_zero` and feeds that to `IsLeftRegular` as an injectivity statement, which unfolds the definition. Mathlib already has `IsLeftRegular.mul_left_eq_zero_iff`, which states exactly `b * a = 0 ↔ a = 0`. The separate `hzero` and the `mul_zero` rewrite are then unnecessary.

Proposed change:

Replace the two lines with
`exact h2.left.mul_left_eq_zero_iff.mp (by linear_combination -h)`
or keep `hzero` and finish with `exact h2.left.mul_left_eq_zero_iff.mp hzero`. Both say "2 is left-regular, so 2 * x = 0 gives x = 0".

Benefit: The cancellation uses a named lemma, so the reader no longer decodes an injectivity argument through `mul_zero`. The proof is shorter and the idea is stated directly.

Source evidence:

- `IsLeftRegular.mul_left_eq_zero_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Algebra/GroupWithZero/Regular.lean`: lemma IsLeftRegular.mul_left_eq_zero_iff (hb : IsLeftRegular b) : b * a = 0 ↔ a = 0

### readable-proof-simplification: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L110-L122)

Declaration: `TauCeti.exists_tendsto_schwarzChristoffelPrimitive_boundary (non-prevertex branch)`

The non-prevertex branch builds the open set `hopen`, then restates the interval membership by hand. It passes through `Metric.ball`, `Real.dist_eq` and `abs_lt` and uses `linarith` three times to convert between `Metric.ball x ε` and `Ioo (x - ε) (x + ε)`. Mathlib already has `Real.ball_eq_Ioo`, which says exactly `ball x r = Ioo (x - r) (x + r)`. The intermediate `hopen`, `hxIoo` and `ha` haves are each used only once.

Proposed change:

Rewrite the ball as an interval once and pass the avoidance fact directly:
```
  · obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp (Set.finite_range a).isClosed.isOpen_compl x hx
    rw [Real.ball_eq_Ioo] at hball
    obtain ⟨L, hL, -, -⟩ := exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀
      (p := x - ε) (q := x + ε) fun i _ hi => hball hi ⟨i, rfl⟩
    exact ⟨L x, hL x ⟨by linarith, by linarith⟩⟩
```
The argument is the same: the prevertices form a closed set avoiding `x`, so a whole interval around `x` has no prevertex, and the edge continuation applies.

Benefit: The proof drops about ten lines and the metric-to-order conversion with `abs_lt`. A reader sees the idea directly: a neighbourhood interval of `x` avoids `range a`, so the edge lemma applies.

Source evidence:

- `Real.ball_eq_Ioo` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Topology/MetricSpace/Pseudo/Defs.lean`: theorem Real.ball_eq_Ioo (x r : ℝ) : ball x r = Ioo (x - r) (x + r)
- `TauCeti.exists_tendsto_schwarzChristoffelPrimitive_sub_eq` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Edge.lean`: {p q : ℝ} (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) :

### readable-proof-simplification: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L240-L248)

Declaration: `TauCeti.collinear_schwarzChristoffelBoundary_image`

The proof shows the two images are equal by a manual `ext`, a `constructor`, and two `rintro`/`exact` blocks. The map and `L` agree pointwise on `Ioo p q`, because `schwarzChristoffelBoundary_eq_of_tendsto` gives `boundary x = L x`. Equal images of agreeing functions is exactly `Set.image_congr`.

Proposed change:

Replace the body after the `obtain` with a single rewrite:
```
  rw [Set.image_congr (g := L) fun x hx =>
    schwarzChristoffelBoundary_eq_of_tendsto a e z₀ x (hL x hx)]
  exact hLcol
```
The proof now says directly that the boundary map and `L` agree on the interval, so their images agree and collinearity transfers.

Benefit: This removes the `convert … using 1`, the `ext`, and the duplicated two-direction membership proof. The remaining step is the pointwise agreement that the mathematics uses.

Source evidence:

- `Set.image_congr` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Data/Set/Image.lean`: theorem image_congr {f g : α → β} {s : Set α} (h : ∀ a ∈ s, f a = g a) : f '' s = g '' s
- `TauCeti.exists_tendsto_schwarzChristoffelPrimitive_injOn_collinear` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Edge.lean`: InjOn L (Ioo p q) ∧ Collinear ℝ (L '' Ioo p q)

### readable-proof-simplification: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L154-L159)

Declaration: `TauCeti.IsSl2System.structureConstant_neg_neg_eq_neg_iff (forward direction)`

The forward direction rewrites the hypothesis hmul, states an auxiliary negated equation with a restated long type ascription, closes it by rewriting backwards with hmul and then ring, and finishes with neg_injective. That is four steps and a duplicated expression for what is a one-line algebraic consequence: from N*N' = -c² and N' = -N, get N² = c².

Proposed change:

Replace the whole bullet with
  · intro h
    linear_combination hx.structureConstant α β γ hγ hαβ * h - hmul
(hmul is left un-rewritten: N * N' = -c², h : N' = -N, goal N² = c²; N*(N' + N) - (N*N' + c²) = N² - c²).

Benefit: It removes the intermediate `have`, the restated type, the `rw ... at` and the `neg_injective` detour. The reader sees directly that the goal is the combination N·h − hmul of the two hypotheses, and the proof no longer depends on the sign-juggling in the auxiliary statement.

Source evidence:

- `structureConstant_mul_structureConstant_neg_neg` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean`:       -(((chainBotCoeff α β + 1 : ℕ) : K) ^ 2) := by

### readable-proof-simplification: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L93-L98)

Declaration: `TauCeti.IsSl2System.structureConstant_mul_structureConstant_neg_neg (hβγ / hγα)`

hγα is the same equation as hβγ with the summands swapped, but it is reproved from scratch with an identical rw/abel script. The repo already derives swapped-summand hypotheses with `.trans (add_comm _ _)`.

Proposed change:

Keep hβγ as is and define
  have hγα : (β : H → K) = (γ : H → K) + ((-α : Weight K H L) : H → K) :=
    hβγ.trans (add_comm _ _)
The comment line "in both orders" then matches the code directly.

Benefit: Drops a duplicated two-line tactic script. The code now states that the second hypothesis is the first with the summands commuted, the same idiom used in structureConstant_skew.

Source evidence:

- `structureConstant_skew` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Basic.lean`: hx.structureConstant β α γ hγ (hαβ.trans (add_comm _ _))

### readable-proof-simplification: [TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean#L115-L116)

Declaration: `discr_eq_one_hundred_twenty_five, ncard_primesOver_five_eq_one, eq_span_zeta_sub_one, ramificationIdx_eq_four, inertiaDeg_eq_one, map_span_five_eq_pow_four`

The same `have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩` line is repeated in six proofs (lines 67, 115, 123, 128, 133, 139). Each of those proofs needs it only so that instance resolution can see the `Fact`. The repetition is boilerplate and hides the real content of each proof, which is one Mathlib lemma applied at `p = 5`.

Proposed change:

Declare the instance once after `namespace TauCeti.NumberField.FifthCyclotomic`, for example `local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩`. Then delete the six `have` lines. This gives, for instance:

`theorem ncard_primesOver_five_eq_one : ... := IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 5 K`

`theorem ramificationIdx_eq_four : 𝔭.ramificationIdx ℤ = 4 := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime 5 K 𝔭`

The `discr` proof becomes `rw [IsCyclotomicExtension.Rat.discr_prime 5 K]; norm_num`.

Benefit: This removes six identical lines, so each proof is a one-line application of the Mathlib lemma. The primality fact is stated once. The repo already does this in other files, so it matches house style.

Source evidence:

- `local instance : Fact (Nat.Prime 5)` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/NumberTheory/NumberField/WorkedExamples/Cubic23/Splitting.lean`: local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
- `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`: theorem ramificationIdx_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :

### readable-proof-simplification: [TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean#L142-L149)

Declaration: `map_span_five_eq_pow_four`

The proof turns `5` into `5 ^ (0 + 1)` twice, using two tactic blocks with the same `rw [zero_add, pow_one]`. The only purpose is to match the shape `p ^ (k + 1)` that `map_eq_span_zeta_sub_one_pow` expects, and a reader has to read both blocks to see that. The `5 ^ (0 + 1)` here is a closed Nat expression and should unfold to `5` by defeq, so the rewriting should be unnecessary.

Proposed change:

Try term-mode proofs: `have hK : IsCyclotomicExtension {5 ^ (0 + 1)} ℚ K := inferInstance` and `have hzeta' : IsPrimitiveRoot (IsCyclotomicExtension.zeta 5 ℚ K) (5 ^ (0 + 1)) := hzeta`. Keep the comment explaining that this is just `p ^ (k + 1)` with `k = 0`. If defeq checking fails on the literal, `by simpa using hzeta` for `hzeta'` and `by simpa` for `hK` are alternatives. The remaining lines (`rw [Nat.cast_ofNat] at h` and the final `rw`) stay unchanged. I have not tested this replacement.

Benefit: The two six-line tactic blocks reduce to two one-line `have`s, so the only visible steps are the key ones. Those are: take the canonical primitive root, apply `map_eq_span_zeta_sub_one_pow` with `k = 0`, and substitute `𝔭 = (ζ - 1)` and `finrank = 4`.

Source evidence:

- `IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`: (map (algebraMap ℤ (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module.finrank ℚ K
- `IsCyclotomicExtension.Rat.ramificationIdx_span_zeta_sub_one'` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`: rw [← pow_one p] at hK hζ

### readable-proof-simplification: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L360-L362)

Declaration: `TauCeti.exists_isSolidTorusNeighborhood (choice of radius r)`

The proof builds an explicit witness `min (ε/2) (δ/2)` and then proves three inequalities by hand with `half_pos`, `half_lt_self`, `min_le_left` and `min_le_right`. All it needs is some `r` with `0 < r < min ε δ`, and the explicit halves hide that.

Proposed change:

Replace the block with
```
obtain ⟨r, hr, hrmin⟩ := exists_between (lt_min hε hδ)
obtain ⟨hrε, hrδ⟩ := lt_min_iff.mp hrmin
```
Here `exists_between` is the density lemma for ordered fields (`DenselyOrdered`). It gives `r` strictly between `0` and `min ε δ`, and `lt_min_iff` splits that into `r < ε` and `r < δ`. Later uses of `hr`, `hrε` and `hrδ` are unchanged.

Benefit: The explicit `min` and halves with their four lemma applications go away. The argument reads as 'pick r positive and below both ε and δ', which is the mathematical content, and the proof is shorter.

Source evidence:

- `exists_between` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Order/Basic.lean`: theorem exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂
- `exists_isOpenEmbedding_normalTube` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Geometry/Manifold/TubularNeighborhood/Euclidean.lean`: ∃ ε > 0, IsOpenEmbedding ((normalTube I f ε).domRestrict fun p : M × V => f p.1 + p.2)

### readable-proof-simplification: [TauCeti/ModelTheory/Scott/RigidGraph.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L103-L111)

Declaration: `TauCeti.rigidSixGraph_iso_eq_refl`

The proof proves a function equality `he` and rewrites with it. That equality holds by definitional unfolding: `toLanguageEquiv_apply` is itself proved by `(rfl)`, and `Function.comp` unfolds. The restated type of `hb`, the `rw [he] at hb`, and the final `h`/`h.symm` pair are therefore bookkeeping. The mathematical content is just: automorphisms preserve level-two back-and-forth equivalence, and level two separates vertices.

Proposed change:

Drop `he`, the `rw`, and the restated type of `hb`:
```lean
  apply RelIso.ext
  intro v
  have hb := e.toLanguageEquiv.bfEquiv (2 : Ordinal.{0}) (fun _ : Fin 1 => v)
  exact ((bfEquiv_two_rigidSixGraph_iff v (e v)).mp hb).symm
```
If elaboration needs help, annotate with `show BFEquiv (L := Language.graph) (2 : Ordinal.{0}) 1 (fun _ => v) (fun _ => e v)` in place of `he`.

Benefit: The proof shrinks from nine lines to about four and states the key idea directly: transport back-and-forth equivalence along the automorphism, then apply the separation lemma. The reader no longer has to follow a function-equality detour that is true by `rfl`.

Source evidence:

- `SimpleGraph.Iso.toLanguageEquiv_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/BackAndForth/Graph.lean`: e.toLanguageEquiv v = e v := (rfl)

### readable-proof-simplification: [TauCeti/ModelTheory/Scott/RigidGraph.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L118-L125)

Declaration: `TauCeti.two_mem_orbitStable_rigidSixGraph`

`ha` and `hb` are `rfl` facts used only to rewrite `h.comp ...` via `simpa` into the form the iff lemma expects. Since the two forms are definitionally equal, both `have`s and the `by simpa only [...]` wrapper are unnecessary. The `subst b; exact BFEquiv.refl β a` ending is fine.

Proposed change:

Pass the restricted equivalence directly:
```lean
  have hab : a = b := funext fun i =>
    (bfEquiv_two_rigidSixGraph_iff (a i) (b i)).mp (h.comp (fun _ : Fin 1 => i))
```
The rest (`subst b; exact BFEquiv.refl β a`) stays as is.

Benefit: This removes two auxiliary equalities and a `simpa`. The remaining one-line term reads as 'restrict the level-two equivalence to coordinate `i`, then use that level two separates vertices', which is the actual argument.

Source evidence:

- `BFEquiv.comp` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/ModelTheory/BackAndForth/Equivalence.lean`: (g : Fin m → Fin n) : BFEquiv (L := L) α m (a ∘ g) (b ∘ g)

### readable-proof-simplification: [TauCeti/ModelTheory/Scott/RigidGraph.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/ModelTheory/Scott/RigidGraph.lean#L135-L140)

Declaration: `TauCeti.orbitRank_rigidSixGraph`

The proof builds a vertex different from `v` by hand, with a case split on `v = 0` and a `decide` side goal. Mathlib already provides `exists_ne` for any nontrivial type, and `Fin 6` is nontrivial, so the case split is avoidable.

Proposed change:

```lean
  obtain ⟨w, hw⟩ := exists_ne v
  exact hw ((bfEquiv_two_rigidSixGraph_iff v w).mp
    (h (fun _ : Fin 1 => w) (bfEquiv_one_rigidSixGraph v w) 2)).symm
```
Here `exists_ne v : ∃ w, w ≠ v`, so the final equation `v = w` has to be flipped with `.symm` before it is applied to `hw`.

Benefit: A four-line ad hoc case analysis becomes one call to a standard lemma. It also makes plain that the argument uses only that the graph has a second vertex, not which one.

Source evidence:

- `exists_ne` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Basic/Nontrivial/Defs.lean`: theorem exists_ne [Nontrivial α] (x : α) : ∃ y, y ≠ x

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

### readable-proof-simplification: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L288-L297)

Declaration: `log_cancellation`

`h1` and `h2` re-prove, almost verbatim, the earlier lemmas `integral_seg1_eq_neg_log` and `integral_seg3_eq_log`. Those lemmas are stated at lines 255–268 for a general `0 < ε < 1`. `h2` even repeats the `integral_comp_sub_left` + `congr 1 <;> ring` argument. As a result the earlier lemmas are never used and the argument is written twice.

Proposed change:

Instantiate the existing lemmas at `ε / r`:
`have h1 := integral_seg1_eq_neg_log (ε / r) hεr_pos hεr_lt1`
`have h2 := integral_seg3_eq_log (ε / r) hεr_pos hεr_lt1`
The types are `∫ t in ε/r..1, (t:ℝ)⁻¹ = -Real.log (ε/r)` and `∫ t in 2..(3 - ε/r), -((3 - t)⁻¹) = Real.log (ε/r)`, which are the shapes `h1c`/`h2c` need. The `h_sub` block and the manual `integral_inv_of_pos`/`Real.log_div` rewrite then disappear, and `h1c`/`h2c` stay unchanged.

Benefit: This removes about ten lines of duplicated calculus. It also gives the earlier lemmas a use, and a reader sees the cancellation as 'segment 1 gives -log δ, segment 3 gives +log δ'.

Source evidence:

- `integral_seg3_eq_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: ∫ t in (2 : ℝ)..(3 - ε), -((3 - t)⁻¹) = Real.log ε
- `integral_seg1_eq_neg_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε

### readable-proof-simplification: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L504-L513)

Declaration: `pv_cutoff_integral_seg1_eq_inv`

The first branch of this proof (lines 506–510) re-derives `1/t` from the curve and its derivative with `rw [sectorCurve_seg1 …, deriv_sectorCurve_seg1 …]; … push_cast; field_simp`. That is exactly the statement of `pv_integrand_seg1`. The sibling lemma `pv_cutoff_F_integrable_delta_1` already uses it in one line (`exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩`). The same duplication occurs for segment 2 (branch at lines ~529–533, inlined `field_simp` instead of `pv_integrand_seg2`) and segment 3 (branch at lines ~560–566, instead of `pv_integrand_seg3`). The same blocks appear again in `pv_cutoff_F_integrable_1_2` and `pv_cutoff_F_integrable_2_3delta`.

Proposed change:

In each `h_on_Ioo`/`h_eq` branch that shows the integrand value, replace the `rw [sectorCurve_segN …, deriv_sectorCurve_segN …]` + nonzero side-conditions + `field_simp` block by the existing lemma. For segment 1:
`· exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩`
For segment 2 use `pv_integrand_seg2 r hr α t ⟨ht1, ht2⟩`. For segment 3 use `pv_integrand_seg3 r hr α t ⟨ht2, h3⟩`, where `h3 : t < 3` is already proved in that branch. The remaining 'norm > ε' branch stays as it is.

Benefit: The proofs become shorter and uniform across the six cutoff lemmas. Each branch states in one line which segment-integrand fact is used, and the `have … ≠ 0` side goals and `push_cast; field_simp` are kept in one place, `pv_integrand_seg*`.

Source evidence:

- `pv_cutoff_F_integrable_delta_1` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩
- `pv_integrand_seg2` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = I * ↑α
- `pv_integrand_seg3` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: (sectorCurve r α t)⁻¹ * deriv (sectorCurve r α) t = -↑((3 - t)⁻¹)

### readable-proof-simplification: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L200-L206)

Declaration: `NumberField.Odlyzko.abs_sinh_le_cosh`

The proof goes through the identity cosh² − sinh² = 1, then `nlinarith`, then `simp_all`, then `sq_le_sq₀`. Mathlib already has `Real.abs_sinh : |sinh x| = sinh |x|`, `Real.cosh_abs`, and `Real.sinh_lt_cosh`. These give the statement directly. The `simp_all` step is also opaque.

Proposed change:

Replace the proof body with:
  rw [Real.abs_sinh, ← Real.cosh_abs x]
  exact (Real.sinh_lt_cosh _).le
The idea is that |sinh x| = sinh |x| < cosh |x| = cosh x. If the `rw` direction proves fiddly, `abs_le.2 ⟨by simpa using (Real.sinh_lt_cosh (-x)).le, (Real.sinh_lt_cosh x).le⟩` is an alternative.

Benefit: The two-line proof states the mathematical reason: sinh < cosh, plus the symmetry in x. It removes `nlinarith` and `simp_all`, and it avoids reproving a fact Mathlib already has.

Source evidence:

- `Real.sinh_lt_cosh` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Complex/Trigonometric.lean`: theorem sinh_lt_cosh : sinh x < cosh x :=
- `Real.abs_sinh` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/SpecialFunctions/Trigonometric/DerivHyp.lean`: theorem abs_sinh (x : ℝ) : |sinh x| = sinh |x| := by
- `Real.cosh_abs` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Complex/Trigonometric.lean`: theorem cosh_abs : cosh |x| = cosh x := by

### readable-proof-simplification: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L681-L687)

Declaration: `NumberField.Odlyzko.abs_poitouKernelSecondDerivative_le`

The last calc step rewrites `|f' x| * c ^ 2` as itself by `rfl`, so it does nothing. The preceding step also proves `|f' x| * c ≤ |f' x| * c ^ 2` with `gcongr; nlinarith`, which is more indirect than needed.

Proposed change:

Delete the line `_ = |f' x| * c ^ 2 := rfl`. For the middle step, use `mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)`. Alternatively, `gcongr` followed by `nlinarith` can be kept as it is.

Benefit: Dropping the vacuous step shortens the calc, and the reader no longer wonders what the final `rfl` line contributes.

Source evidence:

- `NumberField.Odlyzko.abs_poitouKernelSecondDerivative_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: _ = |f' x| * c ^ 2 := rfl

### readable-proof-simplification: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L1053-L1122)

Declaration: `NumberField.Odlyzko.norm_poitouVerticalProfileSecondDerivative_regularized_le`

The nonnegativity fact `hP` (together with its sub-facts `hP₂` and `hP₁`) is proved twice. The first proof is at lines 1053–1072, inside the second calc step. The second is at lines 1108–1122, inside the third calc step. The two proofs are the same `add_nonneg … (sq_nonneg a)` argument with the same expression typed out in full.

Proposed change:

Prove `hP` once, just before `unfold poitouVerticalProfileSecondDerivative` or just after `hk''`. Give the polynomial a name, for example `let P := P₂ + 2 * a * P₁ + a ^ 2` with `P₂` and `P₁` defined at that point. Both calc steps then use the single `hP`, and the second `have hP … ` block (lines 1108–1122) is deleted.

Benefit: This removes about 15 duplicated lines and one place where the two proofs could drift apart. It also makes it clearer that both steps rely on the same positivity fact about the polynomial prefactor.

Source evidence:

- `NumberField.Odlyzko.norm_poitouVerticalProfileSecondDerivative_regularized_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: have hP₂ : 0 ≤ P₂ := by

### readable-proof-simplification: [LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean#L74-L86)

Declaration: `NumberField.Odlyzko.hasDerivAt_integral_tartarAmplitudeDerivativeIntegrand`

The same measurability term, `((continuous_id.neg.mul tartarWeight_continuous).mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable`, is written out twice. The first copy is the `hF_meas` argument and the second is inside the `mono'` argument. Each copy is wrapped in a redundant `by exact`.

Proposed change:

Before the main `exact`, add `have hmeas : ∀ z, AEStronglyMeasurable (tartarAmplitudeDerivativeIntegrand z) volume := fun z ↦ (...).aestronglyMeasurable`. Then pass `.of_forall hmeas` or `Filter.Eventually.of_forall hmeas` for the first argument, and use `hmeas x` inside `mono'`. Also drop the `by exact` wrappers.

Benefit: One named measurability fact replaces two copies of a long term. The shape of the `hasDerivAt_integral_of_dominated_loc_of_deriv_le` call (measurability, integrable bound, derivative bound) is easier to follow.

Source evidence:

- `NumberField.Odlyzko.hasDerivAt_integral_tartarAmplitudeDerivativeIntegrand` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/Odlyzko/ExplicitFormula/RegularizedPoitouQuadraticDecay.lean`: exact abs_mul_tartarWeight_integrable.mono'

### readable-proof-simplification: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L168-L190)

Declaration: `ennreal_mul_rpow (private lemma)`

This 23-line lemma reproves a Mathlib statement. It splits on the sign of e and goes through inverses. It also carries unused hypotheses: `y ≠ ∞` and `y ≠ 0` are anonymous, and the local `heq` is never used. Mathlib's `ENNReal.mul_rpow_of_ne_zero` already gives `(x*y)^z = x^z * y^z` from `x ≠ 0` and `y ≠ 0` alone.

Proposed change:

Delete `ennreal_mul_rpow`. At lines 331–333 use `have hfirst := ENNReal.mul_rpow_of_ne_zero hSn0 hT0 (-(5 - β))` and `have hsecond := ENNReal.mul_rpow_of_ne_zero hSn2_0 hT0 α`. Then `hSnTop` and `hSn2_Top` (lines 303–308) become unused and can be deleted. `hTTop` is still needed at line 345 by `ENNReal.rpow_add`.

Benefit: This removes about 25 lines of sign-case reasoning and unused hypotheses. A reader sees a direct call to the standard Mathlib lemma instead of re-deriving it.

Source evidence:

- `ENNReal.mul_rpow_of_ne_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean`: theorem mul_rpow_of_ne_zero {x y : ℝ≥0∞} (hx : x ≠ 0) (hy : y ≠ 0) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z

### readable-proof-simplification: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L421-L431)

Declaration: `parabolicRieszKernel_tail_le (final calc step with hfun)`

`hfun` equates two lambdas that differ only by redundant parentheses, because `a ^ e * T * N` already parses as `((a ^ e) * T) * N`. It is proved by `funext n; rfl`, so it adds nothing. The `rw [hfun, …]` then `rfl` is also more indirect than needed.

Proposed change:

Replace the block with `by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]; rfl`. Alternatively use `by simp only [ENNReal.tsum_mul_right]; rfl`, or `(ENNReal.tsum_mul_right.trans …)` if you prefer a term. The final `rfl` unfolds `parabolicTailKernelConstant`, as it does now.

Benefit: This removes a vacuous 8-line auxiliary equation. The key idea, pulling the constants `T` and `N` out of the sum, is then the only step shown.

Source evidence:

- `parabolicRieszKernel_tail_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`:           (fun n : ℕ =>
            ((ENNReal.ofReal (2 : ℝ)) ^
              ((n : ℝ) * (β - 5 / q) + 2 * (5 * (1 - 1 / q)))) * T * N) := by
        funext n
        rfl

### readable-proof-simplification: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L144-L160)

Declaration: `positiveShell_pairwise`

The `n < m` and `m < n` cases are the same argument with the roles of n and m swapped. That is about 8 duplicated lines, including the cast steps and the rpow monotonicity step.

Proposed change:

Prove one asymmetric statement, for example `have key : ∀ {a b : ℕ}, a < b → Disjoint (positiveShell R a z) (positiveShell R b z)`. Use `Nat.succ_le_of_lt`, `exact_mod_cast`, `Real.rpow_le_rpow_of_exponent_le` and `mul_le_mul_of_nonneg_right` once. Then finish with `(lt_or_gt_of_ne hnm).elim key (fun h => (key h).symm)`. This also removes the `Set.disjoint_left` rewrite and the `change`.

Benefit: Halving the proof makes the single idea visible: shell a lies below radius 2^(a+1)R ≤ 2^b R, where shell b starts. The symmetric case is clearly just `Disjoint.symm`.

Source evidence:

- `positiveShell_pairwise` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`:   · have hindex : (m : ℤ) + 1 ≤ (n : ℤ) := by
      exact_mod_cast (Nat.succ_le_of_lt hgt)

### readable-proof-simplification: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L133-L139)

Declaration: `RS.taylorCoeffAt_sub`

Subtraction is derived by a roundabout route: build analyticity of `-g`, apply the add lemma, rewrite with `taylorCoeffAt_neg`, prove a function equality by `funext; ring`, then rewrite with `sub_eq_add_neg`. The sibling `taylorCoeffAt_add` instead goes directly through the power-series bridge, and Mathlib has `HasFPowerSeriesAt.sub`, so the same short argument works for subtraction.

Proposed change:

Mirror `taylorCoeffAt_add`:
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  have h := HasFPowerSeriesAt.taylorCoeffAt_eq (hp.sub hq) j
  rw [HasFPowerSeriesAt.taylorCoeffAt_eq hp j, HasFPowerSeriesAt.taylorCoeffAt_eq hq j] 
  exact h  -- the function `f - g` is defeq to `fun z => f z - g z`, and `(p - q).coeff j = p.coeff j - q.coeff j` by `rfl`
(possibly `show taylorCoeffAt (f - g) z₀ j = _` first, then `rw [taylorCoeffAt_eq (hp.sub hq) j, ...]; rfl`). This removes the `hneg`, `h1`, `h2` bookkeeping and `taylorCoeffAt_neg` dependency.

Benefit: Shorter proof with one uniform idea (reduce to power-series coefficients) shared with `taylorCoeffAt_add`; no auxiliary negation lemma or ring-based function equality needed.

Source evidence:

- `HasFPowerSeriesAt.sub` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Analytic/Constructions.lean`: HasFPowerSeriesAt (f - g) (pf - pg) x
- `RS.taylorCoeffAt_add` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: rw [HasFPowerSeriesAt.taylorCoeffAt_eq (hp.add hq) j,

### readable-proof-simplification: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L148-L156)

Declaration: `RS.taylorCoeffAt_fun_sum`

The inductive step proves a separate `hstep` function equality by `funext; rw [Finset.sum_insert ha]` just to rewrite the sum under the lambda binder, then rewrites again with `Finset.sum_insert ha` on the right-hand side.

Proposed change:

Replace `hstep` and the first two rewrites with `simp only [Finset.sum_insert ha]` (which rewrites under the binder and on the RHS), then `rw [taylorCoeffAt_fun_add (hG a (Finset.mem_insert_self a s)) (Finset.analyticAt_fun_sum s fun i hi => hG i (Finset.mem_insert_of_mem hi)), ih fun i hi => hG i (Finset.mem_insert_of_mem hi)]`.

Benefit: Drops a 3-line auxiliary equality; the step reads as 'split off the head term, use additivity, apply induction hypothesis'.

Source evidence:

- `RS.taylorCoeffAt_fun_sum` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: funext z; rw [Finset.sum_insert ha]

### readable-proof-simplification: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L118-L124)

Declaration: `scalarTorusRepresentative_memL2On`

`hcellLe` is never used. The final `exact` uses only `hcubeLe`. The two-sided comparison is built by hand with `restrict_mono_ae`, although the codebase already has `Measure.restrict_congr_set` for exactly this a.e.-equal-sets rewrite.

Proposed change:

Delete `hcellLe`. Replace lines 121–124 with the codebase's usual idiom:
```lean
  rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube] at hbase
  exact hbase
```
If `MemL2On` does not unfold under `exact`, keep one inequality and write `exact hbase.mono_measure (Measure.restrict_mono_ae AVenhance.Infra.Torus.unitCell_ae_eq_unitCube.ge)`.

Benefit: This removes an unused hypothesis and about six lines. The last step then reads as one fact: the open cell and the closed cube differ by a null set. It also matches the idiom used elsewhere in the code.

Source evidence:

- `TestDensityBridge (cell/cube integrability bridge)` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/TestDensityBridge.lean`: rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube] at h
- `AVenhance.Infra.Torus.unitCell_ae_eq_unitCube` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: unitCell 2 =ᵐ[(volume : Measure (Vec 2))] AVenhance.unitCube

### readable-proof-simplification: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L168-L184)

Declaration: `weakPathRepresentative_isPeriodic / weakPathRepresentative_memL2On / weakPathRepresentative_l2NormSq / weakPathRepresentative_pairing_eq_inner`

The same unfolding proof, `funext x; simp [weakPathRepresentative, ...]`, is repeated in four places. These are `isPeriodic` (lines 156–158), `memL2On` (171–173), `l2NormSq` (180–182) and `htheta`'s `hrep` (200–202). The `isPeriodic` case also repeats it for the out-of-range branch. Each time the reader re-checks the same dite-unfolding fact.

Proposed change:

Prove the unfolding fact once, right after the definition:
```lean
theorem weakPathRepresentative_of_mem (u : Icc (0:ℝ) 1 → ScalarTorusL2) (t : Icc (0:ℝ) 1) :
    weakPathRepresentative u t = scalarTorusRepresentative (u t) := by
  funext x; simp [weakPathRepresentative, t.property]
```
Then `weakPathRepresentative_memL2On` becomes `by rw [weakPathRepresentative_of_mem]; exact scalarTorusRepresentative_memL2On (u t)`. `weakPathRepresentative_l2NormSq` and `hrep` in the pairing lemma shrink in the same way. In `isPeriodic`, the in-range branch can use `⟨t, ht⟩` with this lemma.

Benefit: This gives one named, reusable statement of what the representative is at an in-range time. Each downstream proof becomes a rewrite plus the corresponding `scalarTorusRepresentative_*` lemma, which makes the intent clearer and removes about 10 duplicated lines.

Source evidence:

- `weakPathRepresentative_l2NormSq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: simp [weakPathRepresentative, t.property]
- `weakPathRepresentative_pairing_eq_inner` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: have hrep : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by

### readable-proof-simplification: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L289-L294)

Declaration: `isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin (hAE)`

`hAE` only says that the simple extension `K⟮z⟯` lies in an intermediate field that contains `z`. The proof unfolds this to a set inclusion, introduces an arbitrary element, rewrites it to `z`, and substitutes it. Mathlib has a lemma for exactly this statement, so the unfolding is redundant.

Proposed change:

have hAE : A ≤ E.restrictScalars K :=
    IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.mem_adjoin_simple_self F z)

The membership `z ∈ E.restrictScalars K` is definitionally `z ∈ E`, so `mem_adjoin_simple_self F z` should be accepted there.

Benefit: The proof now reads as the underlying argument: `K⟮z⟯ ≤ M` iff `z ∈ M`, and `z ∈ F⟮z⟯`. The singleton case analysis and `subst` disappear.

Source evidence:

- `IntermediateField.adjoin_simple_le_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean`: theorem adjoin_simple_le_iff {K : IntermediateField F E} : F⟮α⟯ ≤ K ↔ α ∈ K
- `IntermediateField.mem_adjoin_simple_self` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean`: theorem mem_adjoin_simple_self : α ∈ F⟮α⟯

### readable-proof-simplification: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L496-L503)

Declaration: `planeCurve_auxiliaryFamily_linearIndependent_of_absoluteIrreducible (final tactic block)`

After `intro`, the hypotheses are named in the context. `apply` is followed by five bullets, and four of them are bare `exact h` passthroughs. This splits one application into goals the reader has to match to arguments by position.

Proposed change:

exact planeCurve_auxiliaryFamily_linearIndependent_of_nonzero_partials
    (p := p) hf hpartialFirst hpartialSecond a b h k ha hh hk
    (irreducible_map_perfectConstantsToFrobeniusSubfield
      (K := K) (L := PlaneCurveFunctionField f) (p := p) f habsolute)
    hdegreeFirst hdegreeSecond hsize hdegreeAlternativeExcluded

Benefit: The call is a single `exact` whose arguments follow the hypothesis order of the target theorem, so the only non-trivial argument, the base-change irreducibility, is easy to spot. The bullet noise goes away.

Source evidence:

- `planeCurve_auxiliaryFamily_linearIndependent_of_nonzero_partials` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: hbaseChange hdegreeFirst hdegreeSecond
      (secondCoordinate_not_mem_frobeniusSubfield

### readable-proof-simplification: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L543-L554)

Declaration: `planeCurve_auxiliaryFamily_linearIndependent_of_absoluteIrreducible_coordinateDegrees (final tactic block)`

This block has the same `apply`-then-bullets pattern. Seven bullets are all `exact` of an already-available fact. This is a plain function application, and the bullets only force the reader to track the goal order.

Proposed change:

exact planeCurve_auxiliaryFamily_linearIndependent_of_absoluteIrreducible
    (p := p) habsolute hpartialFirst hpartialSecond
    (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f) h k
    (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst) hh hk
    (planeCurveFrobeniusRelation_natDegree
      (K := K) (L := PlaneCurveFunctionField f) (p := p) f)
    (transposeBivariate_planeCurveFrobeniusRelation_natDegree
      (K := K) (L := PlaneCurveFunctionField f) (p := p) f)
    hsize hdegreeAlternativeExcluded

Benefit: A direct term mirrors the statement of the target theorem, which takes `0 < a`, `0 < h`, `0 < k`, the two degree identities, the size bound and the exclusion. The reader sees at once which facts feed which hypothesis.

Source evidence:

- `planeCurve_auxiliaryFamily_linearIndependent_of_absoluteIrreducible` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: 0 < a → 0 < h → 0 < k →
      (planeCurveFrobeniusRelation

### readable-proof-simplification: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L267-L269)

Declaration: `planeCurveFrobeniusRelation_irreducible`

The proof is `by exact term`. The same wrapper appears in `hgIrreducible` and `hyTranscendental` in `planeCurve_auxiliaryFamily_linearIndependent`. It adds nothing.

Proposed change:

:=
  hbaseChange.map (planeCurveToBivariate (frobeniusSubfield L p)).toMulEquiv

Similarly, use `have hgIrreducible : Irreducible g := planeCurveFrobeniusRelation_irreducible hbaseChange`.

Benefit: The statements become plain term-mode proofs with no tactic wrapper. The result is slightly shorter and unchanged in meaning.

Source evidence:

- `planeCurve_auxiliaryFamily_linearIndependent` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: have hgIrreducible : Irreducible g := by
    exact planeCurveFrobeniusRelation_irreducible hbaseChange

### readable-proof-simplification: [LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L46-L52)

Declaration: `EulerMeanHarmonic.norm_add_sq_le_twice`

The proof introduces four hypotheses (triangle inequality and three nonnegativity facts) and calls `nlinarith` with a hint to rediscover a standard fact: (x+y)^2 ≤ 2(x^2+y^2) for reals, which Mathlib already has as `add_sq_le`. The nonlinear search hides the simple two-step idea: triangle inequality, then square-add bound.

Proposed change:

Replace the proof with the explicit two-step argument:
  have h := (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2).trans add_sq_le
  linarith
Here `norm_add_le a b : ‖a+b‖ ≤ ‖a‖+‖b‖`, squaring is monotone on nonnegatives, and `add_sq_le : (a+b)^2 ≤ 2*(a^2+b^2)` finishes; `linarith` only distributes the factor 2.

Benefit: Removes the nlinarith call, the manual hint and three unneeded nonnegativity hypotheses. The proof now reads as the mathematical argument (triangle inequality, then (x+y)² ≤ 2(x²+y²)) and no longer depends on a nonlinear arithmetic search.

Source evidence:

- `add_sq_le` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Order/Ring/Basic.lean`: lemma add_sq_le : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
- `pow_le_pow_left₀` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/Order/GroupWithZero/Basic.lean`: theorem pow_le_pow_left₀ [PosMulMono M₀] [MulPosMono M₀]
