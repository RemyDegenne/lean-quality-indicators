@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})

theorem unit_apply (M : PresheafOfModules.{v} R) (V : (Opens Y)ᵒᵖ)
    (m : M.obj V) :
    ((adjunction f R).unit.app M).app V m =
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf).app V m := by
  rw [unit_app_eq f R M, forward_apply f R]
  rfl

end RingedSpaces.Modules.PresheafInverseImage
end
