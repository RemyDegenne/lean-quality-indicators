namespace OAI

namespace GammaFPP.RealDirectionBridge

open PlanarFPP MeasureTheory Filter Set

open scoped Topology

@[simp] theorem latticeEmbed_zero : latticeEmbed 0 = 0 := by ext i; fin_cases i <;> simp [latticeEmbed]

end GammaFPP.RealDirectionBridge
end OAI
