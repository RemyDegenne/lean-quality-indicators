@[expose] public section

namespace BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

theorem weightedSplitTraceLaurent_smooth_of_partialLocalizations
    (alpha beta : K) (d e : ℕ)
    (hspan : Ideal.span {weightedSplitTraceLaurentPartialX alpha beta d e,
        weightedSplitTraceLaurentPartialY alpha beta d e} = ⊤)
    (hX : Algebra.Smooth K
      (Localization.Away (weightedSplitTraceLaurentPartialX alpha beta d e)))
    (hY : Algebra.Smooth K
      (Localization.Away (weightedSplitTraceLaurentPartialY alpha beta d e))) :
    Algebra.Smooth K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by
  let L := WeightedSplitTraceLaurentCoordinateRing alpha beta d e
  let fx : L := weightedSplitTraceLaurentPartialX alpha beta d e
  let fy : L := weightedSplitTraceLaurentPartialY alpha beta d e
  have hXOpen : (PrimeSpectrum.basicOpen fx : Set (PrimeSpectrum L)) ⊆
      Algebra.smoothLocus K L :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hX
  have hYOpen : (PrimeSpectrum.basicOpen fy : Set (PrimeSpectrum L)) ⊆
      Algebra.smoothLocus K L :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hY
  have hLocus : Algebra.smoothLocus K L = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hpx : p ∈ PrimeSpectrum.basicOpen fx
    · exact hXOpen hpx
    by_cases hpy : p ∈ PrimeSpectrum.basicOpen fy
    · exact hYOpen hpy
    have hfx : fx ∈ p.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hpx
    have hfy : fy ∈ p.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hpy
    exfalso
    have hle : Ideal.span {fx, fy} ≤ p.asIdeal := by
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hfx
      · exact hfy
    have hpTop : p.asIdeal = ⊤ := top_unique (hspan ▸ hle)
    exact p.isPrime.ne_top hpTop
  exact ⟨(Algebra.smoothLocus_eq_univ_iff.mp hLocus), inferInstance⟩

end
end BGS.Markoff
end
