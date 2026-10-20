@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})

theorem counit_ι
    (N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R))
    (U : Opens X) (i : index f U)
    (m : ((PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).obj i.left) :
    ((adjunction f R).counit.app N).app (op U)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙
        ((PresheafOfModules.pushforward (F := Opens.map f)
          ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N).presheaf) i) m) =
    N.map i.hom m := by
  rw [counit_app_eq f R N, backward_ι f R]
  rfl

end RingedSpaces.Modules.PresheafInverseImage
end
