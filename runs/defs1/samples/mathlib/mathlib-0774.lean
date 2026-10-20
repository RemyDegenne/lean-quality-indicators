@[expose] public section

noncomputable section

namespace CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

variable {X Y : C}

section

variable [HasZeroMorphisms C]

section

set_option backward.defeqAttrib.useBackward true in
/-- If `F` is an equivalence and `F.map f` is a normal epi, then `f` is a normal epi. -/
@[instance_reducible]
def equivalenceReflectsNormalEpi {D : Type u₂} [Category.{v₁} D] [HasZeroMorphisms D] (F : C ⥤ D)
    [F.IsEquivalence] {X Y : C} {f : X ⟶ Y} (hf : NormalEpi (F.map f)) : NormalEpi f where
  W := F.objPreimage hf.W
  g := F.preimage ((F.objObjPreimageIso hf.W).hom ≫ hf.g)
  w := F.map_injective <| by simp [hf.w]
  isColimit := isColimitOfReflects F <|
    IsColimit.ofCoconeEquiv (Cocone.precomposeEquivalence (compNatIso F))
      (IsColimit.ofIsoColimit
        (IsCokernel.ofIsoComp _ _ (F.objObjPreimageIso hf.W).symm (by simp) hf.isColimit)
          (Cofork.ext (Iso.refl _) (by simp [compNatIso, Cofork.π])))

end
end
end CategoryTheory
end
end
