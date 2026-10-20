@[expose] public section

noncomputable section

namespace NavierStokes.ActualCurrentParticularBounds

open Set Function Filter ProblemStatement WeightedClasses HarmonicCalculus LinearWaveBounds

open scoped Topology ContDiff BigOperators

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E]

theorem mode_jet_bound_local {a : E → ℂ} {Φ : E → ℝ} {x : E}
    (ha : LocalPhysicalCopyBounds.SmoothNear a x)
    (hΦ : LocalPhysicalCopyBounds.SmoothNear Φ x)
    (m : ℕ) {c A B M : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hM : 1 ≤ M) (hc : |c| ≤ M)
    (hab : ∀ i ≤ m, ‖iteratedFDeriv ℝ i a x‖ ≤ A)
    (hΦb : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedFDeriv ℝ i Φ x‖ ≤ B) :
    ∀ k ≤ m, ‖iteratedFDeriv ℝ k
      (fun y => a y * PhysicalGraphBounds.character c (Φ y)) x‖ ≤
        (2 : ℝ) ^ m * A * ((m.factorial : ℝ) * M ^ m * B ^ m) := by
  obtain ⟨a', ha', hea⟩ := ha.exists_global_germ
  obtain ⟨Φ', hΦ', heΦ⟩ := hΦ.exists_global_germ
  have hprod : (fun y => a y * PhysicalGraphBounds.character c (Φ y)) =ᶠ[𝓝 x]
      (fun y => a' y * PhysicalGraphBounds.character c (Φ' y)) := by
    filter_upwards [hea, heΦ] with y hay hφy
    rw [hay, hφy]
  have hφbound := character_comp_positive_jets hΦ' x m hB hM hc (by
    intro i hi him
    rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq heΦ i]
    exact hΦb i hi him)
  intro k hk
  rw [PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hprod k]
  exact PhysicalGraphBounds.pointwise_product_jet_bound ha'
    ((PhysicalGraphBounds.character_smooth c).comp hΦ') x hk hA (by positivity)
    (by intro i hi; rw [← PhysicalWaveSum.iteratedFDeriv_eq_of_eventuallyEq hea i]; exact hab i hi)
    hφbound

end Carrier
end NavierStokes.ActualCurrentParticularBounds
end
end
