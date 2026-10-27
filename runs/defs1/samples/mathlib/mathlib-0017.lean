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

/-- Simple function defined on a finite type. -/
def ofFinite [Finite α] [MeasurableSingletonClass α] (f : α → β) : α →ₛ β where
  toFun := f
  measurableSet_fiber' x := (toFinite (f ⁻¹' {x})).measurableSet
  finite_range' := Set.finite_range f

end Measurable
end SimpleFunc
end MeasureTheory
end
end
