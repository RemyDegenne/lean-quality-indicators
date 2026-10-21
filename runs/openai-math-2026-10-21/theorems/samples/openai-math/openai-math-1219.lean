namespace OAI

section

noncomputable section

open MeasureTheory Filter

open ContinuousLinearMap

open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal

namespace NeutralAtom

theorem RetainedAnalyticFamily.expected_annulus {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] {G : ∀ n, Set (Ω n)}
    (d : RetainedAnalyticFamily (fun n => G n))
    (σ : ∀ n, Ω n → Position → ℝ) (hσ : ∀ n (θ : G n), σ n θ = d.σ n θ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hY : ∀ n, MemLp (fun z => ∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x) 2 (μ n))
    (hY0 : ∀ n, 0 ≤ᵐ[μ n] (fun z => ∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x))
    (hG : ∀ n, MeasurableSet (G n)) {C : ℝ}
    (hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z,
      (∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x)^2 ∂μ n) ≤ C)
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, (∫ x in {x | a < ‖x‖ ∧ ‖x‖ < b}, σ n z x) ∂μ n)
      atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)) := by
  rw [← sommerfeldDensity_annularMass ha hab.le]
  apply d.expected_integral μ σ hσ (isCompact_closedNormAnnulus a b) ?_
    (fun x hx => ⟨hx.1.le,hx.2.le⟩) hY hY0 hG hL2 hbad
  intro hh
  exact (not_le_of_gt ha) (by simpa using hh.1)

end NeutralAtom
end
end
end OAI
