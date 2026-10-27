public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU

open Matrix

variable {K : Type} [Field K]

theorem rot_of_comm_j (G : Matrix (Fin 3) (Fin 3) K)
    (h : G * !![0, 1, 0; -1, 0, 0; 0, 0, 1] = !![0, 1, 0; -1, 0, 0; 0, 0, 1] * G) :
    G 1 1 = G 0 0 ∧ G 1 0 = -G 0 1 := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e00 e01
  exact ⟨by linear_combination -e01, by linear_combination -e00⟩

end CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
end
