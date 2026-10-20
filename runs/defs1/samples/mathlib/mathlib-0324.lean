@[expose] public section

noncomputable section

open Filter Set TopologicalSpace Topology

variable {ι : Sort*} {n : ℕ}

namespace NNReal

variable {α : Type*} {L : SummationFilter α}

section coe

open Filter Finset

/-- `Real.toNNReal` bundled as a continuous map for convenience. -/
@[simps -fullyApplied]
noncomputable def _root_.ContinuousMap.realToNNReal : C(ℝ, ℝ≥0) :=
  .mk Real.toNNReal continuous_real_toNNReal

end coe
end NNReal
end
end
