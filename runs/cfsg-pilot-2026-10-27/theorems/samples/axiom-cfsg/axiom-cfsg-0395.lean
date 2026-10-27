public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section General

variable {G : Type} [Group G] [Finite G]

theorem ggClosure_pair_eq {p : ℕ} (hp : p.Prime) {D : Subgroup G} (hD : Nat.card D = p ^ 2)
    {d y : G} (hd : d ∈ D) (hy : y ∈ D) (hd1 : d ≠ 1) (hdp : d ^ p = 1)
    (hyd : y ∉ Subgroup.zpowers d) : Subgroup.closure {d, y} = D := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.closure ({d, y} : Set G) with hC
  have hCD : C ≤ D := (Subgroup.closure_le D).mpr (by
    intro g hg
    rcases hg with rfl | rfl
    · exact hd
    · exact hy)
  have hdC : d ∈ C := Subgroup.subset_closure (Set.mem_insert d {y})
  have hyC : y ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem d rfl)
  have hzC : Subgroup.zpowers d ≤ C := Subgroup.zpowers_le.mpr hdC
  have hzcard : Nat.card (Subgroup.zpowers d) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hdp hd1]
  obtain ⟨k, hk, hkC⟩ := (Nat.dvd_prime_pow hp).mp (hD ▸ Subgroup.card_dvd_of_le hCD)
  have hpC : p ∣ Nat.card C := hzcard ▸ Subgroup.card_dvd_of_le hzC
  interval_cases k
  · rw [hkC, pow_zero] at hpC
    exact absurd (Nat.le_of_dvd one_pos hpC) (by have := hp.two_le; omega)
  · exfalso
    apply hyd
    have heq : Subgroup.zpowers d = C :=
      Subgroup.eq_of_le_of_card_ge hzC (by rw [hkC, hzcard, pow_one])
    exact heq ▸ hyC
  · exact Subgroup.eq_of_le_of_card_ge hCD (by rw [hD, hkC])

end General
end CFSG.StandardType
end
