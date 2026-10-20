@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})

theorem backward_forward {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (g : (inverseImageFunctor f R).obj M ⟶ N) :
    backward f R (forward f R g) = g := by
  apply (PresheafOfModules.toPresheaf _).map_injective
  change backwardUnderlying f R (forward f R g) =
    (PresheafOfModules.toPresheaf _).map g
  apply (((Opens.map f).op.pointwiseLeftKanExtension M.presheaf).hom_ext_of_isLeftKanExtension
    ((Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf))
  erw [Functor.descOfIsLeftKanExtension_fac]
  change forwardUnderlying f R g ≫
    ((PresheafOfModules.pushforwardCompToPresheaf (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).app N).hom =
    (Opens.map f).op.pointwiseLeftKanExtensionUnit M.presheaf ≫
      (Opens.map f).op.whiskerLeft
        ((PresheafOfModules.toPresheaf _).map g)
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  rfl

end RingedSpaces.Modules.PresheafInverseImage
end
