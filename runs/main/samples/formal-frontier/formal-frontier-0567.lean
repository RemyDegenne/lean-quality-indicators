@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

theorem pointwiseSmul_eq (R : Y.Presheaf RingCat.{v})
    (M : PresheafOfModules.{v} R) (U : Opens X)
    (i : index f U) (r : R.obj i.left) (m : M.obj i.left) :
    pointwiseSmul f R M U
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ R) i) r)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
    (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i)
      (r • m) :=
  (pointwise_smul_ι f R M U i r m).symm

end RingedSpaces.Modules.PresheafInverseImage
end
