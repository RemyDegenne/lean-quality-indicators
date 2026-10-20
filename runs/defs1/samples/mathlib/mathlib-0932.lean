@[expose] public section

variable {l m n α : Type*}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

section Triangular

/-- A lower-block-triangular matrix is invertible if its diagonal is. -/
@[instance_reducible]
def fromBlocksZero₁₂Invertible (A : Matrix m m α) (C : Matrix n m α) (D : Matrix n n α)
    [Invertible A] [Invertible D] : Invertible (fromBlocks A 0 C D) :=
  invertibleOfLeftInverse _
      (fromBlocks (⅟A) 0 (-(⅟D * C * ⅟A))
        (⅟D)) <| by -- a symmetry argument is more work than just copying the proof
    simp_rw [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero,
      Matrix.neg_mul, invOf_mul_self, Matrix.invOf_mul_cancel_right, neg_add_cancel,
      fromBlocks_one]

end Triangular
end CommRing
end Matrix
end
