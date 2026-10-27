public section

namespace CFSG.Monster.Spin

open CFSG.Monster.Code

@[simp] theorem pair_ΩC_thetaD (a : C) : pair ΩC (thetaD a) = 0 := by
  rw [pair_thetaD, θ_ΩC_right]

end CFSG.Monster.Spin
end
