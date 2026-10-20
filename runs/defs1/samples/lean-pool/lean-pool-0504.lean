@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology BigOperators

open NavierStokes.OutgoingProfile (Profile)

namespace NavierStokes.HeatSwitchCone

open StressAlgebra

/-- Qs as an element of `ℝ`. -/
noncomputable def Qs (F : Profile) (XR : ℝ) (c : ℝ → Coeff) (p : Point) : ℝ :=
  -OutgoingHistories.W F.data F.amp p +
    ((1 - F.data.h) * logI F XR c p - axialExponent F.data.h * p.2 *
      derivWithin (fun eta => logI F XR c (p.1, eta)) HeatedOutgoing.parameterDomain p.2 -
      coordinateFactor p.2 * OutgoingHistories.dEta (OutgoingHistories.J F.reset F.amp) p +
      2 * (F.data.h - axialExponent F.data.h) * p.2 * OutgoingHistories.J F.reset F.amp p) /
        (Real.exp (3 * p.1 / 2) * logE F XR c p)

end NavierStokes.HeatSwitchCone
end
end
