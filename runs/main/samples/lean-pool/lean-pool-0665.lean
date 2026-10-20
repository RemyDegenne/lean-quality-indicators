@[expose] public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

lemma det_coeffMat_qP (h : ℕ) : (coeffMat (fun a : Fin h => qP a)).det = ∏ a : Fin h, qlead a := by
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_congr rfl fun a _ => ?_
    simp only [coeffMat, Matrix.of_apply]
    exact coeff_qP_self a
  · intro i j hij
    simp only [coeffMat, Matrix.of_apply]
    apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_qP]
    exact hij

end Zeta5Irrational
end
