public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution

open scoped MatrixGroups commutatorElement

namespace SP3

section General

variable {Y : Type*} [Group Y] [Finite Y]

theorem oddCore_eq_bot_of_isSubnormal_centralizer {U : Subgroup Y} [U.Normal] (hU : IsPGroup 2 U)
    (hC : Subgroup.centralizer (U : Set Y) ≤ U) {z : Y} (hz : z * z = 1) {L : Subgroup Y}
    (hL : IsSubnormal L (Subgroup.centralizer ({z} : Set Y))) :
    classicalInvolutionOddCore ↥L = ⊥ := by
  by_contra hne
  set N : Subgroup ↥L := classicalInvolutionOddCore ↥L with hN
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card L
  have hNn : N.Normal := inferInstance
  have hNnt : Nontrivial N := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hne
  have hdvd : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card N := by
    refine ⟨(Nat.card N).minFac, Nat.minFac_prime ?_, Nat.minFac_dvd _⟩
    have := Finite.one_lt_card (α := N)
    omega
  obtain ⟨p, hp, hpd⟩ := hdvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr hpd)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := N) p hpd
  set g : Y := ((t : ↥L) : Y) with hg
  have hgJ : g ∈ L := (t : ↥L).2
  have hgp : g ^ p ^ 1 = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht] at h
    have := congrArg (fun w : N => (((w : ↥L)) : Y)) h
    simpa [hg] using this
  have hg1 : g ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at ht
    exact hp.one_lt.ne ht
  obtain ⟨x, hx, hnc⟩ := exists_not_commute_of_isSubnormal_centralizer_prime hU hC hz hL hp hp2
    hgJ hgp hg1
  apply hnc
  set x' : ↥L := ⟨x, hx.1⟩ with hx'
  set c : ↥L := (t : ↥L) * x' * (t : ↥L)⁻¹ * x'⁻¹ with hc
  have hcN : c ∈ N := by
    have h1 : x' * (t : ↥L)⁻¹ * x'⁻¹ ∈ N := hNn.conj_mem _ (N.inv_mem t.2) x'
    have h2 := N.mul_mem t.2 h1
    simpa [hc, mul_assoc] using h2
  have hcU : ((c : ↥L) : Y) ∈ U := by
    have : ((c : ↥L) : Y) = (g * x * g⁻¹) * x⁻¹ := by
      simp [hc, hg, hx', mul_assoc]
    rw [this]
    exact U.mul_mem (Subgroup.Normal.conj_mem inferInstance x hx.2 g) (U.inv_mem hx.2)
  obtain ⟨k, hk⟩ := hU ⟨_, hcU⟩
  have hck : c ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have hodd : Odd (orderOf c) := hNodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hcN)
  have hc1 : c = 1 := by
    have h2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd
      ((Nat.coprime_two_right.mpr hodd).pow_right k) h2)
  have h3 : (t : ↥L) * x' = x' * (t : ↥L) := by
    calc (t : ↥L) * x' = c * x' * (t : ↥L) := by rw [hc]; group
      _ = x' * (t : ↥L) := by rw [hc1, one_mul]
  exact congrArg Subtype.val h3

end General
end SP3
end CFSG.ClassicalInvolution.Q3
end
