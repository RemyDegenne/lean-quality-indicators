@[expose] public section

noncomputable section

open Set Function Filter TopologicalSpace ENNReal EMetric Finset

open scoped Topology ENNReal MeasureTheory

variable {α β ι E F 𝕜 : Type*}

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

open SimpleFunc

namespace Lp

open AEEqFun

variable [MeasurableSpace α] [NormedAddCommGroup E] [NormedAddCommGroup F] (p : ℝ≥0∞)
  (μ : Measure α)

variable (E)

variable {E p μ}

namespace simpleFunc

attribute [local instance] simpleFunc.module simpleFunc.normedSpace simpleFunc.isBoundedSMul

section ToSimpleFunc

/-- Find a representative of a `Lp.simpleFunc`. -/
def toSimpleFunc (f : Lp.simpleFunc E p μ) : α →ₛ E :=
  Classical.choose f.2

end ToSimpleFunc
end simpleFunc
end Lp
end MeasureTheory
end
end
