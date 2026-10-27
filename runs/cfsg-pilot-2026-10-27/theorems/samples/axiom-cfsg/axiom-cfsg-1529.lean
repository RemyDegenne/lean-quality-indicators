public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Equiv

open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

open CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem resRM_eq_one_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O}
    (x : (Rbar S g t).subgroupOf S.Mbar) :
    resRM S g haQ t x = 1 ↔ ((x : S.Mbar) : S.O) ∈ Nbar S g t :=
  resV_eq_one_iff haQ _

end CFSG.LargeExtraspecial.S7
end
