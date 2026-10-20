public section

namespace TauCeti

theorem IsConvexSeq.exists_isFiniteFace_of_finiteDomain_eq_Icc {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) {a b : ℕ} (hab : a ≤ b)
    (hdom : ∀ n : ℕ, h n ≠ ⊤ ↔ a ≤ n ∧ n ≤ b) (σ : ℝ) :
    ∃ l u : ℕ, IsFiniteFace h σ l u := by
  let values : Set ℝ :=
    (fun n : ℕ ↦ (h n).untop₀ - σ * n) '' Set.Icc a b
  have hvalues_finite : values.Finite := Set.finite_Icc a b |>.image _
  have hvalues_nonempty : values.Nonempty :=
    ⟨(h a).untop₀ - σ * a, a, ⟨le_rfl, hab⟩, rfl⟩
  have hvalues_bdd : BddBelow values := hvalues_finite.bddBelow
  let c := sInf values
  have hc_mem : c ∈ values := hvalues_nonempty.csInf_mem hvalues_finite
  have hc : IsSupportingLine h σ c := by
    intro n
    by_cases hn : a ≤ n ∧ n ≤ b
    · have hn_top : h n ≠ ⊤ := (hdom n).mpr hn
      rw [← WithTop.coe_untop₀_of_ne_top hn_top, WithTop.coe_le_coe]
      have hle : c ≤ (h n).untop₀ - σ * n :=
        csInf_le hvalues_bdd ⟨n, hn, rfl⟩
      linarith
    · have hn_top : h n = ⊤ := not_ne_iff.mp (mt (hdom n).mp hn)
      simp [hn_top]
  have hface_finite : (supportingFace h σ c).Finite := by
    refine Set.Finite.subset (Set.finite_Icc a b) fun n hn ↦ ?_
    rw [mem_supportingFace] at hn
    exact (hdom n).mp (by rw [hn]; exact WithTop.coe_ne_top)
  have hface_nonempty : (supportingFace h σ c).Nonempty := by
    obtain ⟨n, hn, hnc⟩ := hc_mem
    refine ⟨n, ?_⟩
    rw [mem_supportingFace]
    have hn_top : h n ≠ ⊤ := (hdom n).mpr hn
    rw [← WithTop.coe_untop₀_of_ne_top hn_top, WithTop.coe_eq_coe]
    dsimp [c] at hnc
    linarith
  exact hh.exists_isFiniteFace_of_finite_supportingFace hc hface_finite hface_nonempty

end TauCeti
end
