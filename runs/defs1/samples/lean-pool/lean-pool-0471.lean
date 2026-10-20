@[expose] public section

open Homogenization

open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Choose the unique global flow of a continuous linear differential equation. -/
noncomputable def FiniteSpatialJetGlobal.chosenLinearFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) : ℝ → E → ℝ → E :=
  Classical.choose (existsUnique_linearFlowOn A hA)

end
end AVenhance.Infra.Flow
end
