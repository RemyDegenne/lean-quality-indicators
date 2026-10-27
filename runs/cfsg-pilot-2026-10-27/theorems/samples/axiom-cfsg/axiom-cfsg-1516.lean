public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

section Images

variable {U : Subgroup G} (hU : IsElemAbelian 2 U)

omit [Finite G] in
theorem card_autI_eq_relIndex {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥(autI hU K) = (K ⊓ Subgroup.centralizer (U : Set G)).relIndex K := by
  rw [autI_eq_autOn]
  exact card_autOn_eq_relIndex hK

end Images
end CFSG.Quasithin.Vol2.Ch11.SecB
end
