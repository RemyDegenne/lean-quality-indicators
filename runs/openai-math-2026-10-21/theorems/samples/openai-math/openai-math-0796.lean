namespace OAI

namespace GammaFPP

open MeasureTheory ProbabilityTheory Filter Topology PlanarFPP

namespace SwapGeometry

@[simp] lemma swapStep_swap (d : Step) : swapStep (swapStep d)=d := by cases d <;> rfl

end SwapGeometry
end GammaFPP
end OAI
