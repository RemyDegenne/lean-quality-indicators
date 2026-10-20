@[expose] public section

noncomputable section

namespace NavierStokes.OffplaneCorrectionExtensions

open Set Filter Function

open scoped Topology ContDiff BigOperators

/-- Fiber agreement, given by `EqOn F f (PhysicalMeanDomain.slowDomain (U ∩ positiveSlow))`. -/
def FiberAgreement {V : Type*} (U : Set Slow) (F f : Lift → V) : Prop :=
  EqOn F f (PhysicalMeanDomain.slowDomain (U ∩ positiveSlow))

end NavierStokes.OffplaneCorrectionExtensions
end
end
