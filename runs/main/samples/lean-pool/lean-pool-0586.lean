open Complex Filter Set

open scoped Topology

@[expose] public noncomputable section

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

theorem carlsonLSlit_eq_integral (t : ℂ) {b z : ι → ℂ}
    (hz : z ∈ carlsonRVariableDomain) (hb : b ∈ mvBetaConvergent) :
    carlsonLSlit t b z = carlsonLIntegral t b z := by
  rw [carlsonLSlit_eq_continued t b hz, carlsonLContinued_eq_integral t hz hb]

end DirichletTransform
end
