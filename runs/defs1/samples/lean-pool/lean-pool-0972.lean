public section

open MeasureTheory Set Filter CKN CKN.Foundation.Parabolic

open scoped ENNReal

noncomputable section

namespace ESS

/-- The velocity on each time slice, extended by zero outside the source ball. -/
@[expose] def pressureSplitVelocityExtension (u : ParabolicPoint → Vec3) :
    Vec3 × ℝ → Vec3 := fun z =>
  pressureSplitBall.indicator (fun x : Vec3 => u ((x,z.2) : ParabolicPoint)) z.1

end ESS
end
end
