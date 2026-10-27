public section

namespace CFSG.Quasithin.H13.TorusComm

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

theorem mul_self_eq_one' (h2 : ∀ w : W, w ^ 2 = 1) (w : W) : w * w = 1 := by
  rw [← sq, h2]

end CFSG.Quasithin.H13.TorusComm
end
