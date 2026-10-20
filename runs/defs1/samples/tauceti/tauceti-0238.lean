public section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O] (W : WeierstrassCurve O)

/-- The value of the slope series at a pair of parameters. -/
noncomputable def formalSlopeEval (t₁ t₂ : O) : O :=
  MvPowerSeries.eval₂ (RingHom.id O) (Sum.elim (fun _ ↦ t₁) fun _ ↦ t₂) W.formalSlope

end WeierstrassCurve
end
