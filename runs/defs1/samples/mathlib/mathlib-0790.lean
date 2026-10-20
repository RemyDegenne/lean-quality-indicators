@[expose] public section

noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u u₁

variable {C : Type u₁} [Category.{v} C]

section MorphismRestrict

infixl:85 " ∣_ " => morphismRestrict

variable {X Y : Scheme.{u}}

namespace Scheme.Hom

variable (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of `f.resLE U V` at `x : V` is the stalk map of `f` at `x`. -/
def resLEStalkMap (x : V) :
    Arrow.mk ((f.resLE U V e).stalkMap x) ≅ Arrow.mk (f.stalkMap x) :=
  Arrow.isoMk (U.stalkIso _ ≪≫
      (Y.presheaf.stalkCongr <| Inseparable.of_eq <| by simp)) (V.stalkIso x) <| by
    dsimp
    rw [Category.assoc, ← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq,
      Opens.stalkIso_inv, Opens.stalkIso_inv, ← stalkMap_comp,
      stalkMap_congr_hom _ _ (resLE_comp_ι f e), stalkMap_comp]
    simp

end Scheme.Hom
end MorphismRestrict
end AlgebraicGeometry
end
end
