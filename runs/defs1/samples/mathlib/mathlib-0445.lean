@[expose] public section

namespace Matrix

variable {α n m : Type*}

variable [Mul α] [AddCommMonoid α]

variable (A : Matrix m n α)

open Matrix

/-- `A.HasOrthogonalCols` means matrix `A` has orthogonal columns (with respect to
`dotProduct`). -/
def HasOrthogonalCols [Fintype m] : Prop :=
  HasOrthogonalRows Aᵀ

end Matrix
end
