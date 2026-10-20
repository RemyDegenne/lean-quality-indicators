@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

noncomputable section

namespace AVenhance.Infra.FullTheorem.TransportLimit

open AVenhance.Infra.Parabolic.WeakUniqueness

theorem limit_l2_bound {θ : ℕ → ℝ → Vec 2 → ℝ} {Θ : ℝ → Vec 2 → ℝ}
    (hmem : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (θ j t))
    (hbd : ∀ j, ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (θ j t) ≤ C)
    (hΘ : ∀ t ∈ Set.Icc (0 : ℝ) 1, MemL2On unitCube (Θ t))
    (hunif : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θ j t x - Θ t x)) ≤ η) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, l2NormSq (Θ t) ≤ C := by
  obtain ⟨N, hN⟩ := hunif 1 one_pos
  obtain ⟨C, hC⟩ := hbd N
  refine ⟨2 * C + 2 * 1, fun t ht => ?_⟩
  have h1 : l2NormSq (fun x => θ N t x - Θ t x) ≤ 1 := by
    have := hN N le_rfl t ht
    rw [Real.sqrt_le_left zero_le_one] at this
    simpa using this
  have h2 : l2NormSq (fun x => θ N t x - (θ N t x - Θ t x)) ≤
      2 * l2NormSq (θ N t) + 2 * l2NormSq (fun x => θ N t x - Θ t x) :=
    l2NormSq_sub_le (hmem N t ht) ((hmem N t ht).sub (hΘ t ht))
  have h3 : (fun x => θ N t x - (θ N t x - Θ t x)) = Θ t := by
    funext x; ring
  rw [h3] at h2
  linarith [hC t ht]

end AVenhance.Infra.FullTheorem.TransportLimit
end
end
