@[expose] public section

universe u

namespace Polynomial

theorem exists_monic_irreducible_pow_of_monic_factorization
    {R : Type u} [CommRing R] (I : Ideal R) [I.IsMaximal]
    (hLift : ∀ (F : R[X]) (g₀ h₀ : (R ⧸ I)[X]),
      F.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
      F.map (Ideal.Quotient.mk I) = g₀ * h₀ →
      ∃ g h : R[X], g.Monic ∧ h.Monic ∧ F = g * h ∧
        g.map (Ideal.Quotient.mk I) = g₀ ∧
        h.map (Ideal.Quotient.mk I) = h₀)
    {f : R[X]} (hf : f.Monic) (hirr : Irreducible f) :
    ∃ (q : (R ⧸ I)[X]) (e : ℕ), q.Monic ∧ Irreducible q ∧ 0 < e ∧
      f.map (Ideal.Quotient.mk I) = q ^ e := by
  classical
  let := Ideal.Quotient.field I
  let F := f.map (Ideal.Quotient.mk I)
  have hF : F.Monic := hf.map _
  have hFu : ¬ IsUnit F := not_isUnit_of_natDegree_pos F (by
    simpa only [F, hf.natDegree_map] using hf.natDegree_pos_of_not_isUnit hirr.not_isUnit)
  obtain ⟨q, hq⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors hF.ne_zero hFu
  obtain ⟨hqi, hqm, hqd⟩ := (Polynomial.mem_normalizedFactors_iff hF.ne_zero).mp hq
  -- Separate the largest power of this irreducible from its coprime complement.
  obtain ⟨e, a, hqa, hfac⟩ := WfDvdMonoid.max_power_factor hF.ne_zero hqi
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    exact hqa (by simpa [hfac, he0] using hqd)
  have ham : a.Monic := (hqm.pow e).of_mul_monic_left (hfac ▸ hF)
  obtain ⟨g, h, hgm, hhm, hgh, hg, hh⟩ :=
    hLift f (q ^ e) a hf (hqm.pow e) ham
      ((hqi.coprime_iff_not_dvd.mpr hqa).pow_left) hfac
  -- The lift of the positive power cannot be a unit, so the other lift is 1.
  have ha : a = 1 := by
    rcases hirr.isUnit_or_isUnit hgh with hgu | hhu
    · have hqpow : q ^ e = 1 := by
        rw [← hg, hgm.eq_one_of_isUnit hgu, Polynomial.map_one]
      exact (hqi.not_isUnit (isUnit_of_dvd_one (hqpow ▸ dvd_pow_self q he.ne'))).elim
    · rw [← hh, hhm.eq_one_of_isUnit hhu, Polynomial.map_one]
  exact ⟨q, e, hqm, hqi, he, by simpa [ha] using hfac⟩

end Polynomial
end
