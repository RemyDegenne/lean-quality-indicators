@[expose] public section

noncomputable section

namespace NavierStokes.ProfileHistories

open Set MeasureTheory Filter Metric

open scoped Topology ContDiff

namespace Profiles

open StressAlgebra

variable {D : RadialDomain} (P : Profiles D)

theorem XW_hasDerivAt (h : ℝ) {p : Point} (hp : p ∈ D.carrier) :
    HasDerivAt (fun x => x * P.W h (x, p.2))
      (1 - 2 * axialExponent h * p.2 * P.U p -
        coordinateFactor p.2 * parameterPartial P.U p) p.1 := by
  have hd := ((hasDerivAt_id p.1).sub
    ((primitive_hasDerivAt D P.U_smooth hp).const_mul (2 * axialExponent h * p.2))).sub
      ((primitive_hasDerivAt D (parameterPartial_smooth D P.U_smooth) hp).const_mul
        (coordinateFactor p.2))
  convert! hd using 1
  funext x
  exact P.XW_eq_histories h (x, p.2)

end Profiles
end NavierStokes.ProfileHistories
end
end
