public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {n : ℕ}

lemma omm_sign_eq (z : ZMod 3) (hz : z ≠ 0) : z = 1 ∨ z = -1 := by
  decide +revert

end CFSG.StandardType.FrameRoute.FS81
end
