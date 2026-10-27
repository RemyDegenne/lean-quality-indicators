public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace Proof167Four

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Census

open CFSG.Assembly.RankThreeEven

open scoped commutatorElement

theorem not_small44_card_of_isoLThreePi {X : Type} [Group X] [Finite X] {p e : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (he : 1 ≤ e) (h : Sec4.IsoLThreePi X p e) :
    ¬ Small44 (Nat.card X) := by
  have hp : p.Prime := Fact.out
  set q := p ^ e with hqdef
  set n := Nat.card X with hndef
  have hqmod : q % 3 = 1 ∨ q % 3 = 2 := by
    rcases h with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact Or.inl h1
    · exact Or.inr h2
  have hq3 : q % 3 ≠ 0 := by omega
  have hpne3 : p ≠ 3 := by
    intro h3
    apply hq3
    rw [hqdef, h3]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 3 (by omega))
  have hp5 : 5 ≤ p := by
    have hp3 : 3 ≤ p := by
      have h2 : 2 ≤ p := hp.two_le
      omega
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    omega
  have hq5 : 5 ≤ q := le_trans hp5 (Nat.le_self_pow (by omega) p)
  have hq3bound : 5 * q ^ 2 ≤ q ^ 3 := by
    calc 5 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hq5
      _ = q ^ 3 := by ring
  obtain ⟨A, hA, h3n⟩ : ∃ A : ℕ,
      (A = (q ^ 2 - 1) * (q ^ 3 - 1) ∨ A = (q ^ 2 - 1) * (q ^ 3 + 1)) ∧
        3 * n = q ^ 3 * A := by
    rcases Proof166Res4.three_mul_card_of_isoLThreePi (X := X) he h with h | h
    · exact ⟨_, Or.inl rfl, by simpa [n, q] using h⟩
    · exact ⟨_, Or.inr rfl, by simpa [n, q] using h⟩
  have hq3ge : 125 ≤ q ^ 3 := by
    calc 125 = 5 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq5 3
  have hq2sub : 24 ≤ q ^ 2 - 1 := by
    have h25 : 25 ≤ q ^ 2 := by
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq5 2
    omega
  have hq3sub : 124 ≤ q ^ 3 - 1 := by omega
  have hAge : 2976 ≤ A := by
    rcases hA with rfl | rfl
    · calc 2976 = 24 * 124 := by norm_num
        _ ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := Nat.mul_le_mul hq2sub hq3sub
    · have hq3add : 124 ≤ q ^ 3 + 1 := by omega
      calc 2976 = 24 * 124 := by norm_num
        _ ≤ (q ^ 2 - 1) * (q ^ 3 + 1) := Nat.mul_le_mul hq2sub hq3add
  have hbig : 92160 < n := by
    have h3n' : 3 * n = q ^ 3 * A := h3n
    have hlt : 3 * 92160 < 3 * n := by
      calc 3 * 92160 = 276480 := by norm_num
        _ < 125 * 2976 := by norm_num
        _ ≤ q ^ 3 * A := Nat.mul_le_mul hq3ge hAge
        _ = 3 * n := h3n'.symm
    omega
  have hq3dvdn : q ^ 3 ∣ n := by
    have hcop : Nat.Coprime (q ^ 3) 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by
        intro hd
        exact hq3 (Nat.dvd_iff_mod_eq_zero.mp (Nat.prime_three.dvd_of_dvd_pow hd)))).symm
    have hd : q ^ 3 ∣ 3 * n := by
      rw [h3n]
      exact dvd_mul_right _ _
    exact hcop.dvd_of_dvd_mul_right (by simpa [mul_comm] using hd)
  rintro (⟨r, hrprime, hr3, hrn, hndvd⟩ | h5616 | h92160)
  · have hq3_dvd_rr : q ^ 3 ∣ r * (r ^ 2 - 1) := hq3dvdn.trans hndvd
    have hrne : r ≠ p := by
      intro hrp
      have hp3dvdq3 : p ^ 3 ∣ q ^ 3 := by
        rw [hqdef, ← pow_mul]
        exact pow_dvd_pow p (by omega : 3 ≤ e * 3)
      have hp3dvd : p ^ 3 ∣ p * (p ^ 2 - 1) :=
        hp3dvdq3.trans (by rwa [hrp] at hq3_dvd_rr)
      have hmul : p * p ^ 2 ∣ p * (p ^ 2 - 1) := by
        rwa [show p ^ 3 = p * p ^ 2 by ring] at hp3dvd
      have hp2dvd : p ^ 2 ∣ p ^ 2 - 1 := (Nat.mul_dvd_mul_iff_left hp.pos).mp hmul
      have hpos : 0 < p ^ 2 - 1 := by
        have : 1 < p ^ 2 := by nlinarith [hp.two_le]
        omega
      have hle := Nat.le_of_dvd hpos hp2dvd
      omega
    have hr_not_dvd_q : ¬ r ∣ q := by
      intro hrd
      have hrdp : r ∣ p := by
        have : r ∣ p ^ e := by simpa [hqdef] using hrd
        exact Nat.Prime.dvd_of_dvd_pow hrprime this
      exact hrne ((Nat.prime_dvd_prime_iff_eq hrprime hp).mp hrdp)
    have hcop : Nat.Coprime (q ^ 3) r := by
      refine Nat.Coprime.pow_left 3 ?_
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hrprime).mpr hr_not_dvd_q
    have hq3_dvd_r2sub : q ^ 3 ∣ r ^ 2 - 1 := by
      have hd : q ^ 3 ∣ (r ^ 2 - 1) * r := by simpa [mul_comm] using hq3_dvd_rr
      exact hcop.dvd_of_dvd_mul_right hd
    have hpq3 : q ^ 3 = p ^ (3 * e) := by
      rw [hqdef, ← pow_mul]
      congr 1
      omega
    have hr2sub : r ^ 2 - 1 = (r - 1) * (r + 1) := by
      have h : r ^ 2 = (r - 1) * (r + 1) + 1 := by
        obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        rw [hk]
        simp only [Nat.add_sub_cancel]
        ring
      omega
    have hp3e_dvd : p ^ (3 * e) ∣ (r - 1) * (r + 1) := by
      rwa [hr2sub, hpq3] at hq3_dvd_r2sub
    have hsplit : p ^ (3 * e) ∣ r - 1 ∨ p ^ (3 * e) ∣ r + 1 := by
      by_cases hpdiv : p ∣ r + 1
      · right
        have hpnot : ¬ p ∣ r - 1 := by
          intro hd
          have h2 : p ∣ (r + 1) - (r - 1) := Nat.dvd_sub hpdiv hd
          have h2eq : (r + 1) - (r - 1) = 2 := by omega
          rw [h2eq] at h2
          exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
        have hcop' : Nat.Coprime (p ^ (3 * e)) (r - 1) :=
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpnot).pow_left (3 * e)
        exact hcop'.dvd_of_dvd_mul_left hp3e_dvd
      · left
        have hcop' : Nat.Coprime (p ^ (3 * e)) (r + 1) :=
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpdiv).pow_left (3 * e)
        exact hcop'.dvd_of_dvd_mul_right hp3e_dvd
    have hr_ge : q ^ 3 - 1 ≤ r := by
      rcases hsplit with hd | hd
      · have hle : p ^ (3 * e) ≤ r - 1 := Nat.le_of_dvd (by omega) hd
        rw [← hpq3] at hle
        omega
      · have hle : p ^ (3 * e) ≤ r + 1 := Nat.le_of_dvd (by omega) hd
        rw [← hpq3] at hle
        omega
    have hr_gt : q + 1 < r := by
      have hq3gt : q + 2 < q ^ 3 := by nlinarith [hq3bound, hq5]
      have hq3gt' : q + 1 < q ^ 3 - 1 := by omega
      omega
    have hr_dvd_3n : r ∣ 3 * n := hrn.mul_left 3
    have hr_dvd_prod : r ∣ q ^ 3 * A := by rwa [h3n] at hr_dvd_3n
    have hr_dvd_A : r ∣ A := (hcop.symm).dvd_of_dvd_mul_left hr_dvd_prod
    have hr_not_dvd_q2sub : ¬ r ∣ q ^ 2 - 1 := by
      intro hd
      have hq2eq : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have h : q ^ 2 = (q - 1) * (q + 1) + 1 := by
          obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          rw [hk]
          simp only [Nat.add_sub_cancel]
          ring
        omega
      rw [hq2eq] at hd
      rcases (hrprime.dvd_mul).mp hd with h | h
      · have hle := Nat.le_of_dvd (by omega : 0 < q - 1) h
        omega
      · have hle := Nat.le_of_dvd (by omega : 0 < q + 1) h
        omega
    have hr_dvd_q3sub : r ∣ q ^ 3 - 1 ∨ r ∣ q ^ 3 + 1 := by
      rcases hA with hAeq | hAeq
      · left
        have hd : r ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by rwa [hAeq] at hr_dvd_A
        exact (hrprime.dvd_mul.mp hd).resolve_left hr_not_dvd_q2sub
      · right
        have hd : r ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by rwa [hAeq] at hr_dvd_A
        exact (hrprime.dvd_mul.mp hd).resolve_left hr_not_dvd_q2sub
    have hr_le : r ≤ q ^ 2 + q + 1 := by
      rcases hr_dvd_q3sub with hd | hd
      · have hq3subeq : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
          have h : q ^ 3 = (q - 1) * (q ^ 2 + q + 1) + 1 := by
            obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
            rw [hk]
            simp only [Nat.add_sub_cancel]
            ring
          omega
        have hd' : r ∣ (q - 1) * (q ^ 2 + q + 1) := by rwa [hq3subeq] at hd
        have hr_not_dvd_qsub : ¬ r ∣ q - 1 := by
          intro hd''
          have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hd''
          omega
        have hd'' : r ∣ q ^ 2 + q + 1 :=
          (hrprime.dvd_mul.mp hd').resolve_left hr_not_dvd_qsub
        exact Nat.le_of_dvd (by positivity) hd''
      · have hq3addeq : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
          obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
          rw [hk]
          have hsub : (k + 1) ^ 2 - (k + 1) = k * (k + 1) := by
            have h : (k + 1) ^ 2 = k * (k + 1) + (k + 1) := by ring
            omega
          rw [hsub]
          ring
        have hd' : r ∣ (q + 1) * (q ^ 2 - q + 1) := by rwa [hq3addeq] at hd
        have hr_not_dvd_qadd : ¬ r ∣ q + 1 := by
          intro hd''
          have hle := Nat.le_of_dvd (by omega : 0 < q + 1) hd''
          omega
        have hd'' : r ∣ q ^ 2 - q + 1 :=
          (hrprime.dvd_mul.mp hd').resolve_left hr_not_dvd_qadd
        have hle := Nat.le_of_dvd (by nlinarith [hq5]) hd''
        omega
    have hq3gt : q ^ 2 + q + 2 < q ^ 3 := by nlinarith [hq3bound, hq5]
    omega
  · have hle : n ≤ 5616 := Nat.le_of_dvd (by norm_num) h5616
    omega
  · have hle : n ≤ 92160 := Nat.le_of_dvd (by norm_num) h92160
    omega

end Proof167Four
end CFSG.RankThree.PartTwo.Sec16
end
