namespace OAI

section

section

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory

open scoped ENNReal NNReal Topology BigOperators

namespace HardSphere.PathCutoff

open Wiener FreeVisits

attribute [local irreducible] torusDistance freeTrajectory

lemma regular_reverse {L : Length} (m : ℕ) (r R C : ℝ) (u : Time) (S : ℝ) (ω : ConfigurationPath 1 L) :
    Regular m r R C u S (reverseConfigurationPath 1 L ω) ↔ Regular m r R C u S ω := by
  exact and_congr (meshRegular_reverse m r R C ω) (endpointRegular_reverse u S ω)

end HardSphere.PathCutoff
end
end
end
end OAI
