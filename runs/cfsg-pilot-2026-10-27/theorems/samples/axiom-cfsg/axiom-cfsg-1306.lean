public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

open CFSG.LieType.Multipliers.U43 (F9)

open scoped Matrix

theorem phi9_cj (x : F9) : unitaryInvolution K9 3 1 (phi9r x) = phi9r (cj9 x) := by
  rw [unitaryInvolution_apply, cj9, map_mul, map_mul]
  ring

end CFSG.ClassicalInvolution.Phan.Q3G
end
