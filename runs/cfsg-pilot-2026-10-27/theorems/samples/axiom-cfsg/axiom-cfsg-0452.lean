public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S

open scoped Pointwise

section Config

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_inf_centralizer {L : Subgroup G} {d n : G}
    (hnL : n ∈ Subgroup.normalizer (L : Set G))
    (hnd : n ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    n ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
  have h1 : n⁻¹ * d * n⁻¹⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnd) d).mp (Subgroup.mem_zpowers d)
  have h2 : n⁻¹⁻¹ * d * n⁻¹⁻¹⁻¹ ∈ Subgroup.zpowers d := by
    rw [inv_inv]
    exact (Subgroup.mem_normalizer_iff.mp hnd d).mp (Subgroup.mem_zpowers d)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hxL, hxd⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp hnL x).mp hxL, conj_mem_centralizer_of h1 hxd⟩
  · rintro ⟨hxL, hxd⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hnL x).mpr hxL, ?_⟩
    have := conj_mem_centralizer_of h2 hxd
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at this

end Config
end CFSG.RankThree.PartTwo.Sec4.Ronan148L
end
