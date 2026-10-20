@[expose] public section

open scoped ENNReal

open ProbabilityTheory Set

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

lemma compProd_sum_left {ι : Type*} [Countable ι] {μ : ι → Measure α} [∀ i, SFinite (μ i)] :
    (sum μ) ⊗ₘ κ = sum (fun i ↦ (μ i) ⊗ₘ κ) := by
  rw [compProd, ← Kernel.sum_const, Kernel.compProd_sum_left]
  rfl

end MeasureTheory.Measure
end
