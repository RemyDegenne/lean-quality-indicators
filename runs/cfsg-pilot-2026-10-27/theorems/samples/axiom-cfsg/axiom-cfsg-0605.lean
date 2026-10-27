public section

namespace CFSG.Quasithin.F6

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag AutM12Recog

namespace M12Sylow

theorem psu_three_odd_data64 {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSU 3 p 1) {T : Type} [Group T] [Finite T]
    (hT : TProps64 T) (Q : Sylow 2 S) (n : ℕ) (N : Subgroup T)
    (hQN : Nonempty (↥(Q : Subgroup S) ≃* ↥N)) (hcard : Nat.card T = Nat.card N * 2 ^ n)
    (hA : Nat.card S * 2 ^ n ∣ Nat.card (MulAut S)) : p % 8 = 3 ∧ n = 1 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hS := h
  obtain ⟨⟨-, -, hadm⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 K :=
    ⟨hp, le_rfl, by rw [hK, ← pow_mul, mul_comm]⟩
  let e' : S ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm
  have hP : ordProj[2] (Nat.card S) = ordProj[2] (p - 1) * ordProj[2] (p + 1) ^ 2 := by
    rw [Nat.card_congr e'.toEquiv,
      CFSG.Quasithin.SteinbergCD.ordProj_two_card_unitaryPSU_three hU hp2, pow_one]
  have hout := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (τ := .PSU) (Or.inr rfl) (n := 3) (ℓ := p) (f := 1) (by norm_num) hp le_rfl hS).1
  have hn2 : 2 ^ n ≤ 2 := by
    have h2 := (dvd_card_outer_of_dvd_card_mulAut hA).trans hout
    have hd : CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (p ^ 1) ∣ 3 :=
      Nat.gcd_dvd_left _ _
    have h3 : 2 ^ n ∣ 2 * CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (p ^ 1) := by
      simpa using h2
    exact two_pow_le_two_of_dvd hd h3
  have hn1 : n ≤ 1 := by
    by_contra hlt
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm, hcardS⟩ := Nat.exists_eq_two_pow_mul_odd hS0
  have hPa : ordProj[2] (Nat.card S) = 2 ^ a := ordProj_two_eq hm hcardS
  have h3 := card_mul_two_pow hT (Q : Subgroup S) n N hQN hcard
  rw [card_sylow_eq hm hcardS Q, ← pow_add] at h3
  have han : a + n = 6 := Nat.pow_right_injective le_rfl h3
  have hi1 : 1 ≤ (p - 1).factorization 2 :=
    one_le_factorization_two (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k, by omega⟩)
  have hj1 : 1 ≤ (p + 1).factorization 2 :=
    one_le_factorization_two (by omega) (by obtain ⟨k, hk⟩ := hodd; exact ⟨k + 1, by omega⟩)
  by_cases h16 : 16 ≤ ordProj[2] (p - 1) * ordProj[2] (p + 1)
  · exfalso
    obtain ⟨x, j, hj, hx⟩ := exists_orderOf_two_pow_unitaryPSU' hU hp2 h16
    exact excl64_of_orderOf_sixteen (g := e'.symm x) hj (by rw [MulEquiv.orderOf_eq, hx]) T hT Q
      n N hQN hcard hA
  · have key := u3_arith hi1 hj1 (hP.symm.trans hPa) han hn1 h16
    refine ⟨?_, key.2.2⟩
    have := mod_eight_of_factorization_two (m := p + 1) (by omega) key.2.1
    omega

end M12Sylow
end CFSG.Quasithin.F6
end
