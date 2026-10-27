public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

open Equiv Perm in
theorem cycleType_involution_alt7 (σ : alternatingGroup (Fin 7)) (hσ : orderOf σ = 2) :
    (σ : Perm (Fin 7)).cycleType = {2, 2} := by
  obtain ⟨s, hs'⟩ : ∃ s : Perm (Fin 7), s = (σ : Perm (Fin 7)) := ⟨_, rfl⟩
  rw [← hs']
  have hs2 : orderOf s = 2 := by
    rw [hs']; rw [Subgroup.orderOf_coe]; exact hσ
  have hsign : Perm.sign s = 1 := by rw [hs']; exact mem_alternatingGroup.1 σ.2
  have hall : ∀ n ∈ s.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ orderOf s := Perm.dvd_of_mem_cycleType hn
    rw [hs2] at h1
    have h2 : 2 ≤ n := Perm.two_le_of_mem_cycleType hn
    exact (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2)
  have hrep : s.cycleType = Multiset.replicate (Multiset.card s.cycleType) 2 :=
    Multiset.eq_replicate_of_mem hall
  obtain ⟨k, hk⟩ : ∃ k, k = Multiset.card s.cycleType := ⟨_, rfl⟩
  rw [← hk] at hrep
  have hsum : s.cycleType.sum = 2 * k := by
    rw [hrep]; simp [Multiset.sum_replicate, mul_comm]
  have hsupp : s.support.card = 2 * k := by
    rw [← Perm.sum_cycleType]; exact hsum
  have hle : s.support.card ≤ 7 := by
    calc s.support.card ≤ Fintype.card (Fin 7) := Finset.card_le_univ _
      _ = 7 := by simp
  have hk3 : k ≤ 3 := by omega
  have hk0 : k ≠ 0 := by
    intro h0
    have : s.cycleType = 0 := by rw [hrep, h0]; rfl
    have hs1 : s = 1 := Perm.cycleType_eq_zero.1 this
    rw [hs1, orderOf_one] at hs2
    omega
  have hsg : Perm.sign s = (-1) ^ (s.cycleType.sum + Multiset.card s.cycleType) :=
    Perm.sign_of_cycleType s
  rw [hsum, ← hk, hsign] at hsg
  interval_cases k
  · exact absurd rfl hk0
  · norm_num at hsg
  · rw [hrep]; rfl
  · norm_num at hsg

end CFSG.GH74.GLS.C3.Layer1.Back
end
