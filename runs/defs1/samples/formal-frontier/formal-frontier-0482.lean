@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

/-- The transported module still has the ordinary additive inverse-image sheaf. -/
noncomputable def inverseImageModuleOverActualRingUnderlying (S : Y.Sheaf RingCat.{v})
    (M : SheafOfModules.{v} S) :
    (⟨(inverseImageModuleOverActualRing f S M.val).val.presheaf,
      (inverseImageModuleOverActualRing f S M.val).isSheaf⟩ : X.Sheaf AddCommGrpCat.{v}) ≅
    (TopCat.Sheaf.pullback AddCommGrpCat.{v} f).obj
      (⟨M.val.presheaf, M.isSheaf⟩ : Y.Sheaf AddCommGrpCat.{v}) :=
  inverseImageSheafUnderlyingOfSheaf f S M

end RingedSpaces.Modules.PresheafInverseImage
end
