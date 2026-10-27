public section

namespace CFSG.ComponentClassification.SolMax.FiveCat

open CFSG Subgroup CatLeaf CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem lieModel_of_card_sixty (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {τ : StatedLieTag} {n p f : ℕ} (hadm : StatedLieAdmissible τ n p f) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel X τ n p f) (hX : Nat.card X = 60) : p = 5 := by
  obtain ⟨-, hmul, hfac⟩ := hO X τ n p f hadm hm
  have hp := hadm.1
  have hf := hadm.2.1
  rw [hX] at hmul hfac
  have hdvd : p ^ (lieSylowExponent τ n * f) ∣ 60 := by
    rw [← hfac]
    exact Nat.ordProj_dvd 60 p
  rcases CatLeafProof.lieSylowExponent_ge_three hadm hp2 with ⟨rfl, rfl⟩ | h3
  ·
    obtain ⟨q, hq⟩ : ∃ q, p ^ f = q := ⟨_, rfl⟩
    simp only [lieOrderDivisor, lieOrderNumerator, Finset.Icc_self, Finset.prod_singleton,
      hq] at hmul
    have hqodd : Odd q := hq ▸ (hp.odd_of_ne_two hp2).pow
    have hg : Nat.gcd 2 (q - 1) = 2 :=
      Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one))
    rw [hg, show 2 * (2 - 1) / 2 = 1 from rfl, pow_one] at hmul
    obtain ⟨s, hs⟩ : ∃ s, q ^ 2 = s := ⟨_, rfl⟩
    rw [hs] at hmul
    have hsq : s = q * q := by rw [← hs, sq]
    have hq5 : q ≤ 5 := by
      by_contra hlt
      push Not at hlt
      have h1 : 36 ≤ s := by rw [hsq]; nlinarith
      have h2 : 6 * 35 ≤ q * (s - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    have hq5' : q = 5 := by
      interval_cases q <;> simp_all
    have hpd : p ∣ 5 := by
      rw [← hq5', ← hq]
      exact dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpd
  · exfalso
    have h3f : 3 ≤ lieSylowExponent τ n * f := le_trans h3 (Nat.le_mul_of_pos_right _ hf)
    have h27 : p ^ 3 ∣ 60 := (pow_dvd_pow p h3f).trans hdvd
    have hp3 : p ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have h1 : 4 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
      have h2 := Nat.le_of_dvd (by norm_num) h27
      omega
    have h2 := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · revert h27
      decide

end CFSG.ComponentClassification.SolMax.FiveCat
end
