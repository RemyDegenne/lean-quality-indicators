namespace OAI

namespace SiegelZeros

open scoped BigOperators

open Module

open MvPolynomial

noncomputable section

namespace WeightedTorusJets.Geometry

variable {K R : Type*} [Field K] [Infinite K] [CommRing R] [Algebra K R]

theorem exists_parameters_in_submodule [IsNoetherianRing R] [IsLocalRing R]
    (V : Submodule K R) (h : ℕ)
    (hV : (Ideal.span (V : Set R)).radical = IsLocalRing.maximalIdeal R)
    (hdim : (IsLocalRing.maximalIdeal R).height = h) :
    ∃ s : Finset R, (∀ x ∈ s, x ∈ V) ∧ s.card = h ∧
      (Ideal.span (s : Set R)).radical = IsLocalRing.maximalIdeal R := by
  have hheight : (Ideal.span (V : Set R)).height = h := by
    rw [Ideal.height_eq_inf_minimalPrimes,
      ← (Ideal.span (V : Set R)).radical_minimalPrimes, hV,
      ← Ideal.height_eq_inf_minimalPrimes, hdim]
  obtain ⟨s, hsV, hsc, hsh⟩ := exists_finset_mem_submodule_height V h hheight.ge
  have hsm : Ideal.span (s : Set R) ≤ IsLocalRing.maximalIdeal R := by
    refine (Ideal.span_le.mpr fun x hx => ?_)
    rw [← hV]
    exact Ideal.le_radical (Ideal.subset_span (hsV x hx))
  have hsproper : Ideal.span (s : Set R) ≠ ⊤ := by
    intro ht
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (ht ▸ hsm))
  have hcard : s.card = h := le_antisymm hsc (by
    exact_mod_cast hsh.trans (Ideal.height_span_le_card_of_span_ne_top hsproper))
  refine ⟨s, hsV, hcard, le_antisymm ?_ ?_⟩
  · exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr hsm
  · rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun p hp => ?_
    have : p.IsPrime := hp.isPrime
    have hpheight : (IsLocalRing.maximalIdeal R).height ≤ p.height := by
      rw [hdim]
      exact hsh.trans (Ideal.height_mono hp.le)
    exact (Ideal.eq_of_le_of_height_le p
      (IsLocalRing.le_maximalIdeal hp.isPrime.ne_top) hpheight).ge

end WeightedTorusJets.Geometry
end
end SiegelZeros
end OAI
