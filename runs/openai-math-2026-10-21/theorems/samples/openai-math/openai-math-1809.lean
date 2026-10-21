namespace OAI

open MeasureTheory Set Filter

open scoped BigOperators Topology

namespace DoublingHilbert

open Set Filter MeasureTheory

open scoped Topology

noncomputable section

theorem exists_good_le_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {g : X → ℝ} (hg : Integrable g μ)
    {P : X → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x, P x ∧ g x ≤ ∫ y, g y ∂μ := by
  obtain ⟨x, hx, hbound⟩ := exists_notMem_null_le_integral hg (ae_iff.mp hP)
  exact ⟨x, by simpa using hx, hbound⟩

end
end DoublingHilbert
end OAI
