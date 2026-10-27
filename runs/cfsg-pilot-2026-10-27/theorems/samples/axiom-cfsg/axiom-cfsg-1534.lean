public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6

open CFSG.Quasithin.H13.L32A

open scoped IsMulCommutative

theorem pow_eight_or_three_X2 : ∀ c : SL3.S, SL3.InX2 c → c ^ 8 = 1 ∨ c ^ 3 = 1 := by
  decide +kernel

end CFSG.Quasithin.H13.L14413
end
