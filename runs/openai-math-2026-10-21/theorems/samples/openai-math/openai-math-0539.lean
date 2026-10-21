namespace OAI

noncomputable section

namespace HadwigerCounterexample

open scoped BigOperators

open Matrix Finset

variable {b : ℕ}

variable {p : Shape} {n : ℕ}

theorem mput_apply (s) (Z : BaseMat p n) (i j) : mput p s Z i j =
    monoBit s i.1.val*monoBit s j.1.val*Z i.2 j.2 := by
  classical
  simp [mput,liftM_def,Matrix.mul_apply,transpose_apply,labMat, mul_comm,mul_left_comm,mul_assoc]

end HadwigerCounterexample
end
end OAI
