namespace P2MW.S_AlgebraicCurve_RadialRegion_exists_window_perimeter

set_option autoImplicit false

open scoped Real

open AlgebraicCurve Set

noncomputable section

namespace GridWindow

namespace WinData

variable (D : WinData)

theorem J_pos : 0 < D.J := by
  unfold J
  have := D.hj
  omega

end WinData
end GridWindow
end
end P2MW.S_AlgebraicCurve_RadialRegion_exists_window_perimeter
