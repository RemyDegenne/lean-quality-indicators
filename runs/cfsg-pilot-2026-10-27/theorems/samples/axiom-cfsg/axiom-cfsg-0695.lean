public section

namespace CFSG.RankThree.PartOne.KS.ScalFive

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension

open scoped Matrix

variable {G : Type*} [Group G] {n : ℕ}

namespace ScalRel

variable {q : Fin n → G} {z s t : G} {M Sm : Matrix (Fin n) (Fin n) (ZMod 5)} {i₀ j₀ : Fin n}
  {cs : Fin n → ℕ} {r : ZMod 5} {ct : Fin n → ℕ}
  (hR : ScalRel q z s t M Sm i₀ j₀ cs r ct)

include hR

section Finite

variable [Finite G]

section Quot

variable [((QG q).subgroupOf (HG q s t)).Normal]

omit [Finite G] in
theorem tb_pow : ((⟨t, t_mem_H⟩ : HG q s t) : HG q s t ⧸ (QG q).subgroupOf (HG q s t)) ^ 4 = 1 := by
  rw [← QuotientGroup.mk_pow, mk_eq_one_iff]
  show t ^ 4 ∈ QG q
  rw [hR.t_pow]
  exact one_mem _

end Quot
end Finite
end ScalRel
end CFSG.RankThree.PartOne.KS.ScalFive
end
