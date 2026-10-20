@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.PresheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

theorem pointwiseMap_ι {R : Y.Presheaf RingCat.{v}}
    {M N : PresheafOfModules.{v} R} (φ : M ⟶ N)
    (U : Opens X) (i : index f U) (m : M.obj i.left) :
    (pointwiseMap f φ).app (op U)
      ((colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i) m) =
    (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ N.presheaf) i)
      (φ.app i.left m) := by
  change (colimit.ι (CostructuredArrow.proj (Opens.map f).op (op U) ⋙ M.presheaf) i ≫
    (pointwiseMap f φ).app (op U)).hom m = _
  erw [colimit.ι_map]
  rfl

end RingedSpaces.Modules.PresheafInverseImage
end
