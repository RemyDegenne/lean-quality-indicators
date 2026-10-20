@[expose] public section

namespace RS

open Finset Matrix

theorem det_rowOp (ℓ : ℕ) : (rowOp ℓ).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (rowOp_blockTriangular ℓ)]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [rowOp]

end RS
end
