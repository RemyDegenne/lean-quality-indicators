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

### vacuity-and-misstatement: [Mathlib/Data/Finsupp/PWO.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/Finsupp/PWO.lean#L20-L21)

Declaration: `module docstring (Main statements) vs Finsupp.wellQuasiOrderedLE`

The module docstring names a main statement `Finsupp.isPWO`. It describes it as holding for a fintype index and a codomain that is a well-ordered linear order. No such declaration exists in the file. A grep of the Mathlib tree finds `Finsupp.isPWO` only in this docstring. The only result in the file is the instance `Finsupp.wellQuasiOrderedLE`. That instance has different hypotheses: `Finite σ` instead of `Fintype σ`, and a `Preorder` with `WellQuasiOrderedLE` instead of a well-ordered linear order. Its conclusion is `WellQuasiOrderedLE (σ →₀ α)` rather than an `IsPWO` statement about a set. A reader following the documentation would look for a nonexistent theorem. They would also believe the result needs a linear order, which is a stricter condition than the file proves.

Proposed change:

Rewrite the 'Main statements' entry to describe the actual result. For example: `* Finsupp.wellQuasiOrderedLE` - Dickson's lemma: `σ →₀ α` is well-quasi-ordered when `σ` is finite and `α` is a well-quasi-ordered preorder with `Zero`. Update the introductory paragraph to say 'finite type' and 'well-quasi-ordered preorder' instead of 'fintype' and 'linear order that is well ordered'. If the `Set.IsPWO` formulation is still wanted, state it explicitly. It can be obtained from the instance via `WellQuasiOrderedLE`/`IsPWO` lemmas, but I have not checked which lemma names apply.

Benefit: The documentation would match the declared result and its true generality. Readers and search tools would no longer look for a missing `Finsupp.isPWO`. They would also see that the result needs only a preorder and a finite index type.

Source evidence:

- `Finsupp.wellQuasiOrderedLE` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/Finsupp/PWO.lean`: instance Finsupp.wellQuasiOrderedLE {α σ : Type*} [Zero α] [Preorder α] [WellQuasiOrderedLE α]
    [Finite σ] : WellQuasiOrderedLE (σ →₀ α) :=

### fragile-proofs: [TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean#L51-L59)

Declaration: `TauCeti.gradedIdempotentHeadBasis`

The two side-condition proofs use `classical` followed by `simpa`. The cited lemma already gives exactly `... = if j = i then 1 else 0`. The goal is instead `(headFamily he₀ i).obj.smulGradedDimension (e j) = 0` (or `= 1`), where `headFamily` is a private abbrev. The proof therefore relies on the default simp set to unfold the abbrev and the FullSubcategory projection. It also relies on simp to reduce the `if` with the supplied `hji`, and to rewrite the goal and the hypothesis into the same normal form. A routine change to simp lemmas for `smulGradedDimension`, `Pairwise`, or `FullSubcategory.obj` could leave the goal and the hypothesis in different forms. The `classical` call is needed only to supply the lemma's `[DecidableEq I]` argument. It gives no mathematical content, and the `if` condition is then stated with a classical instance.

Proposed change:

Drop `simpa` and use the lemma's own statement as a term, so the `if` is reduced by the explicit lemmas `if_neg hji` and `if_pos rfl`. For example, the first obligation could be `fun j i hji => by classical; exact (smulGradedDimension_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan j i (hne i)).trans (if_neg hji)`, and the second `... .trans (if_pos rfl)`. This relies on `headFamily i`.obj being definitionally `gradedPositiveMulQuotient 𝒜 (he₀ i)`, which holds for the abbrev. Alternatively, `rw [lemma, if_neg hji]` can be used.

Benefit: The proof depends only on the public statement of `smulGradedDimension_gradedIdempotentHead` and on `if_neg`/`if_pos`. It no longer depends on how simp normalizes the goal. A reader can also see that the hypotheses are just the Kronecker-delta statement specialized to `j ≠ i` and `j = i`.

Source evidence:

- `TauCeti.smulGradedDimension_gradedIdempotentHead` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Category/GradedModuleCat/Idempotent/Head.lean`: (gradedPositiveMulQuotient 𝒜 (he₀ i)).smulGradedDimension (e j) = if j = i then 1 else 0
- `TauCeti.gradedSimpleClassBasis` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/SimpleBasis.lean`: (hne : Pairwise fun i j => (S j).obj.smulGradedDimension (e i) = 0)

### readable-proof-simplification: [TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/Idempotent/Head.lean#L69-L79)

Declaration: `TauCeti.gradedIdempotentHeadBasis_apply and TauCeti.gradedIdempotentHeadBasis_repr_apply`

Each of the two lemmas has a proof that is just `by exact <term>`. The `by exact` wrapper adds a tactic block around what is already a complete term proof. The upstream lemmas `gradedSimpleClassBasis_apply` and `gradedSimpleClassBasis_repr_apply` are themselves stated as term proofs or plain rewrites, so the wrapper adds nothing.

Proposed change:

Write the proofs as terms. For the first lemma, replace `:= by\n  exact gradedSimpleClassBasis_apply _ _ _ _ _ _ i` with `:=\n  gradedSimpleClassBasis_apply _ _ _ _ _ _ i`. For the second lemma, replace `:= by\n  exact gradedSimpleClassBasis_repr_apply _ _ _ _ _ _ x i` with `:=\n  gradedSimpleClassBasis_repr_apply _ _ _ _ _ _ x i`.

Benefit: The proofs read directly as "this is the general lemma specialised to the head family". There is no tactic-mode noise, and the style matches the term-mode proof of the upstream lemma `gradedSimpleClassBasis_apply`.

Source evidence:

- `TauCeti.gradedSimpleClassBasis_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/SimpleBasis.lean`:   Module.Basis.mk_apply _ _ i
- `TauCeti.gradedSimpleClassBasis_repr_apply` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Category/GradedModuleCat/CartanMap/SimpleBasis.lean`: gradedIdempotentCoordinate (he i) (he₀ i) x := by
