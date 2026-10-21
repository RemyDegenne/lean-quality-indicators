namespace OAI

namespace Ostmann

open scoped BigOperators Classical

theorem finite_positive_heavy_cells (P I : Finset ℕ) (label : ℕ → ℕ) (μ f : ℕ → ℝ)
    (hlabel : ∀ p ∈ P, label p ∈ I) (hμ : ∀ p ∈ P, 0 ≤ μ p)
    (hf : ∀ p ∈ P, f p ≤ 1) (δ θ M : ℝ) (hδ : 0 ≤ δ) (hθ : 0 ≤ θ)
    (hbias : δ * (∑ p ∈ P, μ p) ≤ ∑ p ∈ P, μ p * f p)
    (hthin : I.card * θ ≤ (δ / 4) * ∑ p ∈ P, μ p)
    (hcap : ∀ h ∈ I, finiteCellMass P label μ h ≤ M) :
    (δ / 4) * (∑ p ∈ P, μ p) ≤
      (positiveHeavyCells I (finiteCellMass P label μ) (finiteCellMean P label μ f) δ θ).card * M := by
  have hh := positiveHeavyCells_card I (finiteCellMass P label μ) (finiteCellMean P label μ f)
    δ θ M (fun h _ => finiteCellMass_nonneg P label μ hμ h) hδ hθ
    (fun h _ => finiteCellMean_le_one P label μ f hμ hf h)
    (by rw [finiteCellMass_sum P I label μ hlabel, finiteCellMean_sum P I label μ f hlabel hμ]; exact hbias)
    (by rw [finiteCellMass_sum P I label μ hlabel]; exact hthin) hcap
  rwa [finiteCellMass_sum P I label μ hlabel] at hh

end Ostmann
end OAI
