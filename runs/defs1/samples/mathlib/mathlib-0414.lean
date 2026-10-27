@[expose] public section

universe v u

open CategoryTheory Opposite TopologicalSpace Topology

namespace AlgebraicGeometry

namespace IsClosedImmersion

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of closed subschemes is contravariantly equivalent
to the lattice of ideal sheaves. -/
noncomputable
def overEquivIdealSheafData (X : Scheme.{u}) :
    (MorphismProperty.Over @IsClosedImmersion ⊤ X)ᵒᵖ ≌ X.IdealSheafData where
  functor := (MorphismProperty.Over.forget _ _ _).op ⋙ X.kerFunctor
  inverse :=
  { obj I := .op <| .mk _ I.subschemeι inferInstance
    map {I J} h := (MorphismProperty.Over.homMk (Scheme.IdealSheafData.inclusion h.le)).op
    map_comp f g := Quiver.Hom.unop_inj (by ext1; simp) }
  unitIso := NatIso.ofComponents (fun Y ↦
    letI : IsClosedImmersion Y.unop.hom := Y.unop.prop
    ((MorphismProperty.Over.isoMk (asIso Y.unop.hom.toImage).symm).op)) fun {X Y} f ↦ by
      apply Quiver.Hom.unop_inj
      ext1
      dsimp
      rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq,
        ← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
      simp
  counitIso := NatIso.ofComponents (fun I ↦ eqToIso (by simp))

end IsClosedImmersion
end AlgebraicGeometry
end
