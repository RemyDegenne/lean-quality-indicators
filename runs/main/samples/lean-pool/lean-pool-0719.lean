@[expose] public section

open scoped InnerProductSpace

namespace TauCeti

namespace DavisKahan

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem realSpectrum_specRestrict_Icc_subset
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {l r : ℝ} :
    TauCeti.LinearPMap.realSpectrum
        (selfAdjointSpectralRestriction A hA (Set.Icc l r) measurableSet_Icc)
      ⊆ Set.Icc l r := by
  intro lam hlam
  by_contra hcon
  rw [Set.mem_Icc] at hcon
  push Not at hcon
  have havoid : ∀ a b : ℝ, Set.Icc l r ∩ Set.Ioo a b = ∅ → lam ∈ Set.Ioo a b → False := by
    intro a b hdisj hmem
    have := selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
      A hA (Set.Icc l r) measurableSet_Icc hdisj lam hmem
    rw [realSpectrum_eq_spectraSpectrum] at hlam
    exact this hlam
  rcases lt_or_ge lam l with h | h
  · refine havoid (lam - 1) l ?_ ⟨by linarith, h⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hx1, -⟩, -, hx4⟩
    linarith
  · have hr : r < lam := hcon h
    refine havoid r (lam + 1) ?_ ⟨hr, by linarith⟩
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, hx2⟩, hx3, -⟩
    linarith

end DavisKahan
end TauCeti
end
