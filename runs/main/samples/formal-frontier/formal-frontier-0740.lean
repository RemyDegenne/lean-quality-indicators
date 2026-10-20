@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
theorem pointwiseToPullbackFac (C : Type (v + 1)) [Category.{v} C]
    [HasColimits C] (P : Y.Presheaf C) :
    (Opens.map f).op.pointwiseLeftKanExtensionUnit P ≫
      (Opens.map f).op.whiskerLeft
        (PresheafInverseImage.pointwiseToPullback f C P).hom =
      (Opens.map f).op.leftKanExtensionUnit P :=
  by
    simpa only [PresheafInverseImage.pointwiseToPullback,
      Functor.leftKanExtensionUnique, Functor.leftKanExtensionUniqueOfIso,
      Iso.refl_hom, Category.id_comp] using
      (Functor.descOfIsLeftKanExtension_fac
        (α := (Opens.map f).op.pointwiseLeftKanExtensionUnit P)
        (G := (Opens.map f).op.leftKanExtension P)
        (β := (Opens.map f).op.leftKanExtensionUnit P))

end RingedSpaces.Modules.SheafInverseImage
end
