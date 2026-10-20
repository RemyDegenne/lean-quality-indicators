@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped Topology ContDiff BigOperators

open NavierStokes.OutgoingProfile

namespace NavierStokes.NominalProfile

theorem outgoing_axis_halfKernel (F : Profile) (R eta : ℝ) (hR : 0 < R) :
    F.axisDatum eta = -(∫ x in Ioi 0, halfKernel (OutgoingDilation.E F R) eta x) := by
  have ha := congrFun (OutgoingDilation.axisDatum_unchanged F R hR) eta
  simp only [OutgoingDilation.axisDatum, OutgoingDilation.canonicalKernel] at ha
  simp_rw [halfKernel_eq]
  rw [integral_div]
  linear_combination -ha

end NavierStokes.NominalProfile
end
end
