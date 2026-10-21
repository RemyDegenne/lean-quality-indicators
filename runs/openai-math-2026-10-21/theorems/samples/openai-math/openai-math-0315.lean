namespace OAI

namespace BFSSQuantum.AlgebraData

noncomputable section

open BFSSSpinHalf

open scoped Kronecker

variable {N : ℕ} (M : AlgebraData N)

lemma massT_spinHalf (a : Fin 3) : BFSSGamma.massT M.gamma*M.spinHalf a =
    (1/2 : ℝ) • M.gamma (Fin.castLE (by decide) a) := by
  simp only [spinHalf,mul_smul_comm,←mul_assoc,
    BFSSGamma.massT_sq M.gamma M.gamma_clifford M.gamma_symmetric,neg_mul,one_mul,smul_neg]
  module

end
end BFSSQuantum.AlgebraData
end OAI
