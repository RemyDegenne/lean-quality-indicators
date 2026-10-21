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
