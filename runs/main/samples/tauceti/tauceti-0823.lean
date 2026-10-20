public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

universe u v w

variable {X₁ : Type u} {X₂ : Type v} {Y₁ : Type w} {Y₂ : Type*}
  [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
  {c₁ : X₁ × Y₁ → ℝ≥0∞} {c₂ : X₂ × Y₂ → ℝ≥0∞}
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν₁ : Measure Y₁} {ν₂ : Measure Y₂}
  {π₁ : Measure (X₁ × Y₁)} {π₂ : Measure (X₂ × Y₂)}

section Separable

variable [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
  [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]

protected theorem IsOptimalCoupling.prod (hc₁ : Measurable c₁) (hc₂ : Measurable c₂)
    (h₁ : IsOptimalCoupling c₁ π₁ μ₁ ν₁) (h₂ : IsOptimalCoupling c₂ π₂ μ₂ ν₂) :
    IsOptimalCoupling (fun z : (X₁ × X₂) × Y₁ × Y₂ ↦ c₁ (z.1.1, z.2.1) + c₂ (z.1.2, z.2.2))
      ((π₁.prod π₂).map fun w ↦ ((w.1.1, w.2.1), (w.1.2, w.2.2))) (μ₁.prod μ₂) (ν₁.prod ν₂) := by
  have : IsProbabilityMeasure π₁ := h₁.toIsCoupling.isProbabilityMeasure
  have : IsProbabilityMeasure π₂ := h₂.toIsCoupling.isProbabilityMeasure
  refine ⟨h₁.toIsCoupling.prodProdProdComm h₂.toIsCoupling, ?_⟩
  rw [lintegral_map_prodProdProdComm hc₁ hc₂, h₁.lintegral_eq, h₂.lintegral_eq,
    transportCost_prod_add hc₁ hc₂]

end Separable
end TauCeti
end
end
