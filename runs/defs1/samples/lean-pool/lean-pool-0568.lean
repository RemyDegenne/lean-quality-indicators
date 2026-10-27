section

@[expose] public section

noncomputable section

namespace NavierStokes.ActivationHolomorphic

open Set Filter Metric MeasureTheory Complex

open scoped Topology ContDiff

open NaturalAxisCoefficients NaturalEntrance

/-- Radial jet, given by `iteratedDeriv k (fun x => F (x,p.2)) p.1`. -/
def radialJet (F : CField) (k : ℕ) (p : CPoint) : ℂ :=
  iteratedDeriv k (fun x => F (x,p.2)) p.1

end NavierStokes.ActivationHolomorphic
end
end
end
