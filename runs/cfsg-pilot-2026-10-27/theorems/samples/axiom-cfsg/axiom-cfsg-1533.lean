public section

namespace CFSG.Semidihedral.LocalPrimeFailure

open CFSG.Open CFSG.DihedralBlueprint

variable {G : Type} [Group G]

theorem factorization_two_eq_of_odd_factor [Finite G] {K M D : Subgroup G} (hMK : M ≤ K)
    (hDK : D ≤ K) (hM : (M.subgroupOf K).Normal) (hodd : Odd (Nat.card M))
    (hfac : ∀ x ∈ K, ∃ m ∈ M, ∃ c ∈ D, m * c = x) :
    (Nat.card K).factorization 2 = (Nat.card D).factorization 2 := by
  let M' := M.subgroupOf K
  let D' := D.subgroupOf K
  have hsup : M' ⊔ D' = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨m, hm, c, hc, rfl⟩ := hfac x hx
    exact Subgroup.mul_mem_sup (show (⟨m, hMK hm⟩ : K) ∈ M' from hm)
      (show (⟨c, hDK hc⟩ : K) ∈ D' from hc)
  have h1 : M'.relIndex D' * Nat.card M' = Nat.card K := by
    rw [← Subgroup.relIndex_sup_left, hsup, Subgroup.relIndex_top_right,
      Subgroup.index_mul_card]
  have h2 : M'.relIndex D' ∣ Nat.card D' := M'.relIndex_dvd_card D'
  have hcM : Nat.card M' = Nat.card M := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMK).toEquiv
  have hcD : Nat.card D' = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv
  rw [hcM] at h1
  rw [hcD] at h2
  have hr : M'.relIndex D' ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  apply le_antisymm
  · rw [← h1, Nat.factorization_mul hr Nat.card_pos.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]
    exact (Nat.factorization_le_iff_dvd hr Nat.card_pos.ne').mpr h2 2
  · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hDK) 2

end CFSG.Semidihedral.LocalPrimeFailure
end
