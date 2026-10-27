@[expose] public section

noncomputable section

open Set hiding restrict restrict_apply

open Filter ENNReal

open Function (support)

open NNReal ENNReal MeasureTheory

open scoped Topology

namespace MeasureTheory

variable {α β γ δ : Type*}

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

section Measurable

variable [MeasurableSpace α]

/-- Simple function defined on the empty type. -/
def ofIsEmpty [IsEmpty α] : α →ₛ β := ofFinite isEmptyElim

end Measurable
end SimpleFunc
end MeasureTheory
end
end
