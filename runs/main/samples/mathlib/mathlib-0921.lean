@[expose] public section

open scoped ENNReal

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

@[simp] lemma compProd_zero_left (κ : Kernel α β) : (0 : Measure α) ⊗ₘ κ = 0 := by simp [compProd]

end MeasureTheory.Measure
end
