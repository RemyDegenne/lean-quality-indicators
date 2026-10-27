public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.G2U

open CFSG.RankThree.PartTwo.Sec4.RonanK432 (H8 sp8Z sp8T sp8E)

open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb IsSylowOf Cen CenS Nor)

section General

variable {G : Type} [Group G]

theorem card_of_isSylowOf [Finite G] {p : ℕ} (hp : p.Prime) {H P : Subgroup G}
    (h : IsSylowOf p P H) : Nat.card P = p ^ (Nat.card H).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hle, hpg, hcop⟩ := h
  obtain ⟨a, ha⟩ := hpg.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P H
  rw [inf_of_le_left hle, ha] at h1
  have hne : P.relIndex H ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hf : (P.relIndex H).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop)
  rw [← h1, Nat.factorization_mul hne (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply, hf,
    Nat.Prime.factorization_pow hp, Finsupp.single_eq_same, zero_add, ha]

end General
end CFSG.RankThree.PartTwo.Sec21.FF81.Sp8
end
