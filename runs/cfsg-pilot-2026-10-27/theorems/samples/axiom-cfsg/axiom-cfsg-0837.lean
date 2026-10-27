public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

open CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

theorem quotHom_mk {t : S.O} {X : Submodule (ZMod 2) S.Qt}
    (hX : ∀ x ∈ Rbar S g t, ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ X) (x : Rbar S g t)
    (w : S.Qt) :
    quotHom S g t X hX x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) :=
  rfl

end CFSG.LargeExtraspecial.S6
end
