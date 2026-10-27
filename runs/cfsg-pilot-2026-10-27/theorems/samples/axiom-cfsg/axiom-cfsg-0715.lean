public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

open scoped Pointwise

theorem eq_one_of_mul_self_eq_one_of_two_eq_zero {K : Type*} [Field K] (h2 : (2 : K) = 0)
    {ε : K} (hε : ε * ε = 1) : ε = 1 := by
  have h : (ε - 1) ^ 2 = 0 := by linear_combination hε + (1 - ε) * h2
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)

end CFSG.LieType.Chevalley
end
