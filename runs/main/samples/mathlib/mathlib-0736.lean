@[expose] public section

open Real

noncomputable section

namespace Real

namespace Angle

@[simp]
theorem sign_coe_pi_div_two : (↑(π / 2) : Angle).sign = 1 := by
  rw [sign, sin_coe, sin_pi_div_two, sign_one]

end Angle
end Real
end
end
