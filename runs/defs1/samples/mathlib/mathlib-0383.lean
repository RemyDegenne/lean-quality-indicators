@[expose] public section

variable {l m n α : Type*}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

section Block

/-- A block matrix is invertible if the top left corner and the corresponding Schur complement
is. -/
@[instance_reducible]
def fromBlocks₁₁Invertible (A : Matrix m m α) (B : Matrix m n α) (C : Matrix n m α)
    (D : Matrix n n α) [Invertible A] [Invertible (D - C * ⅟A * B)] :
    Invertible (fromBlocks A B C D) := by
  -- we argue by symmetry
  letI := fromBlocks₂₂Invertible D C B A
  letI iDCBA :=
    submatrixEquivInvertible (fromBlocks D C B A) (Equiv.sumComm _ _) (Equiv.sumComm _ _)
  exact
    iDCBA.copy' _
      (fromBlocks (⅟A + ⅟A * B * ⅟(D - C * ⅟A * B) * C * ⅟A) (-(⅟A * B * ⅟(D - C * ⅟A * B)))
        (-(⅟(D - C * ⅟A * B) * C * ⅟A)) (⅟(D - C * ⅟A * B)))
      (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm
      (fromBlocks_submatrix_sum_swap_sum_swap _ _ _ _).symm

end Block
end CommRing
end Matrix
end
