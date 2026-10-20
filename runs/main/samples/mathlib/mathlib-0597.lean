@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped Simplicial

namespace SSet

variable (X : SSet.{u})

variable {n : ℕ}

namespace Subcomplex

variable {X} (A : X.Subcomplex)

lemma eq_top_iff_contains_nonDegenerate :
    A = ⊤ ↔ ∀ (n : ℕ), X.nonDegenerate n ⊆ A.obj _ := by
  simpa using! le_iff_contains_nonDegenerate ⊤ A

end Subcomplex
end SSet
end
