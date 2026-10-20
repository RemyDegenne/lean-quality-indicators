@[expose] public section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

section CompositionProduct

variable {s : Set (β × γ)}

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₖ " => ProbabilityTheory.Kernel.compProd

@[simp]
theorem compProd_of_not_isSFiniteKernel_left (κ : Kernel α β) (η : Kernel (α × β) γ)
    (h : ¬ IsSFiniteKernel κ) :
    κ ⊗ₖ η = 0 := by
  simp [compProd, h]

end CompositionProduct
end Kernel
end ProbabilityTheory
end
