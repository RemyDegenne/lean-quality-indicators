public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra

/-- An extension `L / K` **splits** the `K`-algebra `A` when the scalar extension `L ⊗[K] A` is a
full matrix algebra over `L`.

The matrix size is existentially quantified so that the predicate makes sense for an arbitrary
`K`-algebra. For a finite-dimensional central simple `A` it is not a choice: it is forced to be
`TauCeti.Algebra.deg K A` by `TauCeti.Algebra.IsSplittingField.nonempty_algEquiv_matrix_deg`. -/
def IsSplittingField (K A L : Type*) [Field K] [Ring A] [Algebra K A] [Field L] [Algebra K L] :
    Prop :=
  ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

end Algebra
end TauCeti
end
