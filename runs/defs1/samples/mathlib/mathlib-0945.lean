@[expose] public section

universe w v u

namespace CategoryTheory

open Category Opposite Limits Abelian

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

namespace GrothendieckTopology.MayerVietorisSquare

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})

variable (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

open ComposableArrows

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Comparison isomorphism from the Mayer-Vietoris sequence and the
contravariant sequence of `Ext`-groups. -/
noncomputable def sequenceIso : S.sequence F n₀ n₁ h ≅
    Ext.contravariantSequence S.shortComplex_shortExact F n₀ n₁ (by omega) :=
  isoMk₅ (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _) (Iso.refl _)
    ((AddCommGrpCat.biprodIsoProd _ _).trans (Ext.biprodAddEquiv.symm).toAddCommGrpIso)
    (Iso.refl _)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)
    (by dsimp; rw [comp_id, id_comp]; rfl)
    (by ext; apply biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply)
    (by ext; symm; apply mk₀_f_comp_biprodAddEquiv_symm_biprodIsoProd_hom)

end GrothendieckTopology.MayerVietorisSquare
end CategoryTheory
end
