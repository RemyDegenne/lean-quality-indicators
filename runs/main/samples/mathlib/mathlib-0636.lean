@[expose] public section

variable {l m n α : Type*}

namespace Matrix

open scoped Matrix

section CommRing

variable [Fintype l] [Fintype m] [Fintype n]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n]

variable [CommRing α]

section Det

theorem det_add_mul {A : Matrix m m α} (U : Matrix m n α)
    (V : Matrix n m α) (hA : IsUnit A.det) :
    (A + U * V).det = A.det * (1 + V * A⁻¹ * U).det := by
  nth_rewrite 1 [← Matrix.mul_one A]
  rwa [← Matrix.mul_nonsing_inv_cancel_left A (U * V), ← Matrix.mul_add,
    det_mul, ← Matrix.mul_assoc, det_one_add_mul_comm, ← Matrix.mul_assoc]

end Det
end CommRing
end Matrix
end
