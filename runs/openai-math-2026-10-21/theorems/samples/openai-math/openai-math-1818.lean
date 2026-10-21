namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

section

attribute [instance] TracialStage.cstar TracialStage.order TracialStage.starOrder

namespace TracialStage

variable (X : TracialStage)

lemma infinite : ¬ FiniteDimensional ℂ X := by
  intro h
  exact carInfiniteDimensional (Module.Finite.of_injective X.base.toLinearMap X.base_injective)

end TracialStage
end
end NaimarkZFC
end
end OAI
