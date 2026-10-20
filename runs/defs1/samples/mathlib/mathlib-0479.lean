@[expose] public section

universe v₁ v₂ v₂' u₁ u₂ u₂'

namespace CategoryTheory

variable {C₁ C₂ D₁ D₂ H : Type*}
  [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂] [Category* H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₁' : MorphismProperty D₁} {W₂' : MorphismProperty D₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

variable {Φ}

variable (Φ)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories
`(Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
def LeftResolution.opEquivalence (X₂ : C₂) :
    (Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂) where
  functor := LeftResolution.opFunctor Φ X₂
  inverse := (RightResolution.unopFunctor Φ (Opposite.op X₂)).rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end LocalizerMorphism
end CategoryTheory
end
