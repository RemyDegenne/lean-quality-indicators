@[expose] public section

noncomputable section

namespace NavierStokes.CommonCoverSolve

open Set Function Filter MeasureTheory

open scoped Topology ContDiff BigOperators InnerProductSpace

open TorusInverse

namespace Geometry

variable (g : Geometry)

/-- Path bound, given by `(coveringBound D * ‖(g.basis : Plane →L[ℝ] Plane)‖) * (‖(g.basis.symm
: Plane →L[ℝ] Plane)‖ * coveringBound D)`. -/
noncomputable def pathBound (D : ℕ) : ℝ :=
  (coveringBound D * ‖(g.basis : Plane →L[ℝ] Plane)‖) *
    (‖(g.basis.symm : Plane →L[ℝ] Plane)‖ * coveringBound D)

end Geometry
end NavierStokes.CommonCoverSolve
end
end
