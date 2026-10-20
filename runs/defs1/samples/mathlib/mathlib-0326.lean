@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}

namespace Functor

/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps!]
def toEssImageCompι (F : C ⥤ D) : F.toEssImage ⋙ F.essImage.ι ≅ F :=
  ObjectProperty.liftCompιIso _ _ _

end Functor
end CategoryTheory
end
end
