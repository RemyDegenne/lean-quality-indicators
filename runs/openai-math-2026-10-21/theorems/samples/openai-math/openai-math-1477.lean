namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology

open scoped NNReal

theorem compact_moments_extend_on_ball {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    (a : Ambient d) (R : ℝ)
    (hμ : ∀ j, ∀ᵐ x ∂μ j, x ∈ ball a R) (hν : ∀ᵐ x ∂ν, x ∈ ball a R)
    (w : ℕ → Ambient d → ℝ) (v : Ambient d → ℝ)
    (hmoment : ∀ (ψ : Ambient d → ℝ) (L A : ℝ≥0), HasCompactSupport ψ →
      LipschitzWith L ψ → (∀ x, |ψ x| ≤ (A : ℝ)) →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν))) :
    ∀ (ψ : Ambient d → ℝ) (L : ℝ≥0), LipschitzWith L ψ →
      Tendsto (fun j => ∫ x, w j x * ψ x ∂μ j) atTop (𝓝 (∫ x, v x * ψ x ∂ν)) := by
  intro ψ L hψ
  obtain ⟨g, K, B, hgc, hgLip, hgB, heq⟩ := exists_compact_lipschitz_test_on_ball a R ψ L hψ
  have hm : ∀ j, (∫ x, w j x * g x ∂μ j) = ∫ x, w j x * ψ x ∂μ j := by
    intro j
    apply integral_congr_ae
    filter_upwards [hμ j] with x hx
    rw [heq x hx]
  have hn : (∫ x, v x * g x ∂ν) = ∫ x, v x * ψ x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [heq x hx]
  simpa only [hm, hn] using! hmoment g K B hgc hgLip hgB

end
end RieszRectifiability
end OAI
