public section

namespace CFSG.LieType.OutStructure

open Subgroup

open CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.ComponentClassification.PerfectAutomorphisms

variable {X : Type*} [Group X] {L : Subgroup X} [L.Normal]

theorem conjQuotientHom_apply (x : X) :
    conjQuotientHom (L := L)
        (QuotientGroup.mk' (L ⊔ Subgroup.centralizer (L : Set X)) x) =
      conjOuterHom (L := L) x := by
  simp [conjQuotientHom]

end CFSG.LieType.OutStructure
end
