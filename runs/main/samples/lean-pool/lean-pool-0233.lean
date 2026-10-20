@[expose] public section

noncomputable section PortComputability

open MeasureTheory Set

namespace MarkovProcess

section

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]

theorem denseRestriction_injective [T2Space alpha] :
    Function.Injective (denseRestriction (alpha := alpha)) := by
  intro omega eta h
  apply ContinuousMap.ext
  have heq : (omega : NNReal → alpha) = eta :=
    denseRange_castOrderEmbedding.equalizer omega.continuous eta.continuous h
  exact congrFun heq

end ContinuousPath
end
end MarkovProcess
end PortComputability
end
