# Findings

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
