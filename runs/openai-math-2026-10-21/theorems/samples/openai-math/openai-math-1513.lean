namespace OAI

section

noncomputable section

namespace UniformKServer.StarMovementData

open Finset StarRanks StarSchedules StarLower StarOutputData StarOutputFeasibility StarAllocator

open scoped Classical

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι] {k : ℕ}

theorem dominant_active (d : Data Ω ι k) (t : ℕ) (ω : Ω) (o : ι)
    (ho : EpochGeometry.dominant (epoch d StarConstants.delta t ω)=some o) : 0 < held d t ω o := by
  have hp := (EpochGeometry.dominant_spec ho).1
  have hh := (EpochGeometry.dominant_size (epoch_valid d StarConstants.delta t ω) ho).1
  linarith

end UniformKServer.StarMovementData
end
end
end OAI
