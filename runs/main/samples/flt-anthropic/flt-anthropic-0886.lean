namespace P2MW.S_AlgebraicCurve_RadialRegion_exists_window_perimeter

set_option autoImplicit false

open scoped Real

open AlgebraicCurve Set

noncomputable section

namespace GridWindow

namespace WinData

variable (D : WinData)

theorem left_pt_mem_perimPts {h : ℝ} (hh : D.IsHt D.jlo h) : (⟨D.X₀, h⟩ : ℂ) ∈ D.perimPts := by
  rcases hh with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
  · exact D.left_mem_perimPts hm
  · exact D.leftC_mem_perimPts hm

end WinData
end GridWindow
end
end P2MW.S_AlgebraicCurve_RadialRegion_exists_window_perimeter
