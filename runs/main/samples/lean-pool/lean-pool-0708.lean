@[expose] public section

noncomputable section

open Set Filter Function MeasureTheory

open scoped ContDiff Topology BigOperators

open NavierStokes.OutgoingProfile (Profile)

open NavierStokes.OutgoingDilation (switchRadius patchRadius patchRatio compensationPatch
    shapedPatchAmplitude)

namespace NavierStokes.HeatedOutgoing

theorem heatE_pos (F : Profile) (XR eta X : ℝ) (hX : 0 < X) (heta : eta ∈ parameterDomain) :
    0 < heatE F XR (X, eta) :=
  mul_pos (OutgoingDilation.positive F XR _) (HeatTailEdit.multiplier_bounds F.data.h_pos
    (ParametricHeatTail.diffusion_mem heta).1 hX).1

end NavierStokes.HeatedOutgoing
end
end
