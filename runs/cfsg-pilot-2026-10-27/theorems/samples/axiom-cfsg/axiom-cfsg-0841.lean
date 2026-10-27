public section

namespace CFSG.GF2Type.Aschbacher1976Full.Shape

open CFSG CFSG.SectionRank.Ccomm CFSG.Blueprint Subgroup

open scoped commutatorElement

section Frattini

variable {P : Type*} [Group P] [Finite P] {D E R : Subgroup P} {z : P}

theorem four_lt_index_frattini (hP : IsPGroup 2 P) (c : CritData D E R z)
    (hk8 : 8 ≤ Nat.card (Zof D)) {w : ℕ} (hw : 1 ≤ w) (hEcard : Nat.card E = 2 ^ (1 + 2 * w))
    (hER : E ⊓ R = zpowers z) : 4 < (frattini P).index := by
  haveI : Fact (IsPGroup 2 P) := ⟨hP⟩
  haveI := c.R_normal
  haveI : Fact (IsPGroup 2 ↥R) := ⟨hP.to_subgroup R⟩
  obtain ⟨a, k, hag⟩ := exists_gen hP c
  have hk : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hag.card] at this
    omega
  set N : Subgroup P := (frattini ↥R).map R.subtype with hN
  have hNR : N ≤ R := Subgroup.map_subtype_le _
  have hZR : Zof D ≤ R := c.RZ.symm.le.trans inf_le_left
  have hsqR : ∀ r ∈ R, r ^ 2 ∈ N := fun r hr =>
    Subgroup.mem_map.mpr
      ⟨(⟨r, hr⟩ : ↥R) ^ 2, pth_power_mem_frattini_of_isPGroup (R := ↥R) (p := 2) ⟨r, hr⟩, rfl⟩
  have hzN : z ∈ N := by
    rw [hag.z_eq c (by omega)]
    have hb : a ^ 2 ^ (k - 2) ∈ R := hZR (pow_mem hag.mem _)
    have h2 : (a ^ 2 ^ (k - 2)) ^ 2 = a ^ 2 ^ (k - 1) := by
      rw [← pow_mul, ← pow_succ]
      congr 2
      omega
    rw [← h2]
    exact hsqR _ hb
  have hzpN : zpowers z ≤ N := zpowers_le.mpr hzN
  have hsq : ∀ x : P, x ^ 2 ∈ N := by
    intro x
    have hx : x ∈ E ⊔ R := by rw [c.ER]; exact mem_top x
    obtain ⟨e, he, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hx
    have hcr : Commute e r := c.E_R_comm he hr
    rw [hcr.mul_pow]
    exact mul_mem (hzpN (c.E_sq e he)) (hsqR r hr)
  have hcomm : ∀ x y : P, ⁅x, y⁆ ∈ N := by
    intro x y
    have hx : x ∈ E ⊔ R := by rw [c.ER]; exact mem_top x
    have hy : y ∈ E ⊔ R := by rw [c.ER]; exact mem_top y
    obtain ⟨e₁, he₁, r₁, hr₁, rfl⟩ := mem_sup_of_normal_right.mp hx
    obtain ⟨e₂, he₂, r₂, hr₂, rfl⟩ := mem_sup_of_normal_right.mp hy
    have h := commutator_mul_mul (c.E_R_comm he₁ hr₁ : Commute e₁ r₁) (c.E_R_comm he₁ hr₂)
      (c.E_R_comm he₂ hr₁) (c.E_R_comm he₂ hr₂)
    rw [commutatorElement_def, h]
    refine mul_mem (hzpN (c.E_comm e₁ he₁ e₂ he₂)) ?_
    have h1 : (⁅(⟨r₁, hr₁⟩ : ↥R), ⟨r₂, hr₂⟩⁆ : ↥R) ∈ frattini ↥R :=
      commutator_le_frattini_of_isPGroup (p := 2) (by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (mem_top _) (mem_top _))
    exact Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
  have hΦ : frattini P ≤ N := by
    rw [frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
    rintro g (hg | ⟨x, rfl⟩)
    · have : commutator P ≤ N := by
        rw [_root_.commutator_def, Subgroup.commutator_le]
        intro x _ y _
        exact hcomm x y
      exact this hg
    · exact hsq x
  have hRidx : 4 ≤ R.index := by
    have h1 : R.relIndex (E ⊔ R) = R.relIndex E := Subgroup.relIndex_sup_right E R
    rw [c.ER, Subgroup.relIndex_top_right] at h1
    have h2 : Nat.card (R.subgroupOf E) * (R.subgroupOf E).index = Nat.card E :=
      Subgroup.card_mul_index _
    have h3 : Nat.card (R.subgroupOf E) = 2 := by
      have h7 : Nat.card ((R.subgroupOf E).map E.subtype) = Nat.card (R.subgroupOf E) :=
        Subgroup.card_map_of_injective E.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_comm, hER, Nat.card_zpowers, c.z_ord] at h7
      exact h7.symm
    have h4 : R.relIndex E = (R.subgroupOf E).index := rfl
    rw [h3, hEcard] at h2
    rw [h1, h4]
    have h5 : 2 ^ (1 + 2 * w) = 2 * 2 ^ (2 * w) := by rw [pow_add, pow_one]
    have h6 : 2 ^ 2 ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrel : N.relIndex R = (frattini ↥R).index := by
    have : N.subgroupOf R = frattini ↥R :=
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective _
    exact congrArg Subgroup.index this
  have hfr : 2 ≤ (frattini ↥R).index := by
    have hne : (frattini ↥R).index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one] at h
      have h1 : (⊥ : Subgroup ↥R) = ⊤ := lemma_1_7_a (p := 2) ⊥ (by rw [bot_sup_eq]; exact h)
      have h2 : (⟨z, hZR c.z_mem⟩ : ↥R) ∈ (⊥ : Subgroup ↥R) := h1 ▸ mem_top _
      have h3 : z = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp h2)
      have := c.z_ord
      rw [h3, orderOf_one] at this
      omega
    have := Subgroup.index_ne_zero_of_finite (H := frattini ↥R)
    omega
  have hNidx : 8 ≤ N.index := by
    have := Subgroup.relIndex_mul_index hNR
    rw [hrel] at this
    calc 8 = 2 * 4 := by norm_num
      _ ≤ (frattini ↥R).index * R.index := Nat.mul_le_mul hfr hRidx
      _ = N.index := this
  have hdvd : N.index ∣ (frattini P).index := Subgroup.index_dvd_of_le hΦ
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd
  omega

end Frattini
end CFSG.GF2Type.Aschbacher1976Full.Shape
end
