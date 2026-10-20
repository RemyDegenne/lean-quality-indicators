public section

namespace TauCeti

open Topology

theorem _root_.IsLocalMinOn.hasDerivWithinAt_Iic_nonpos {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : f' ≤ 0 := by
  simpa using h.neg.hasDerivWithinAt_Iic_nonneg hf.neg

end TauCeti
end
