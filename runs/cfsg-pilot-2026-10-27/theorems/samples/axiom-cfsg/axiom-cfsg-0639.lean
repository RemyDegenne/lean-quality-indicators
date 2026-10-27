public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2

open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

namespace TransvectionConfig

variable {q : QuadraticForm (ZMod 2) V} {a : V} {W : Submodule (ZMod 2) V}
  {L : Subgroup (V ≃ₗ[ZMod 2] V)} (C : TransvectionConfig q a W L)

include C

theorem formK_apply (ψ : Module.Dual (ZMod 2) W) (hψ : ψ ⟨a, C.haW⟩ = 0) (w : W) :
    C.formK ψ hψ (Submodule.Quotient.mk w) = ψ w := rfl

end TransvectionConfig
end CFSG.LargeExtraspecial
end
