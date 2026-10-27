public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates Equiv Equiv.Perm Matrix

theorem involution_conj_alt9 {σ : Perm (Fin 9)} (hs : sign σ = 1) (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) :
    ∃ π : Perm (Fin 9), sign π = 1 ∧ (π * σ * π⁻¹ = aPerm ∨ π * σ * π⁻¹ = dtPerm) := by
  obtain ⟨hrep, hcard⟩ := cycleType_involution_alt9 hs h2 h1
  obtain ⟨hrepA, hcardA⟩ := cycleType_involution_alt9 (σ := aPerm) (by decide) (by decide)
    (by decide)
  obtain ⟨hrepD, hcardD⟩ := cycleType_involution_alt9 (σ := dtPerm) (by decide) (by decide)
    (by decide)
  have hsuppA : aPerm.support.card = 8 := by decide
  have hsuppD : dtPerm.support.card = 4 := by decide
  have hA4 : Multiset.card aPerm.cycleType = 4 := by
    have h := sum_cycleType aPerm
    rw [hrepA, Multiset.sum_replicate, smul_eq_mul, hsuppA] at h
    omega
  have hD2 : Multiset.card dtPerm.cycleType = 2 := by
    have h := sum_cycleType dtPerm
    rw [hrepD, Multiset.sum_replicate, smul_eq_mul, hsuppD] at h
    omega
  rcases hcard with h | h
  · obtain ⟨π, hπ, he⟩ := exists_even_conj (τ := dtPerm)
      (isConj_iff_cycleType_eq.2 (by rw [hrep, hrepD, h, hD2])) (by decide)
    exact ⟨π, hπ, Or.inr he⟩
  · obtain ⟨π, hπ, he⟩ := exists_even_conj (τ := aPerm)
      (isConj_iff_cycleType_eq.2 (by rw [hrep, hrepA, h, hA4])) (by decide)
    exact ⟨π, hπ, Or.inl he⟩

end CFSG.Sporadic.ThSchreier
end
