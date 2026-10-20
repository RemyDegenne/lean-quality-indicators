@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y) (R : Y.Presheaf RingCat.{v})

theorem backward_ι {M : PresheafOfModules.{v} R}
    {N : PresheafOfModules.{v} ((Opens.map f).op.pointwiseLeftKanExtension R)}
    (h : M ⟶ (PresheafOfModules.pushforward (F := Opens.map f)
      ((Opens.map f).op.pointwiseLeftKanExtensionUnit R)).obj N)
    (U : Opens X) (i : index f U) (m : M.obj i.left) :
    (backward f R h).app (op U)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
    N.map i.hom (h.app i.left m) :=
  backwardUnderlying_ι f R h U i m

end RingedSpaces.Modules.PresheafInverseImage
end
