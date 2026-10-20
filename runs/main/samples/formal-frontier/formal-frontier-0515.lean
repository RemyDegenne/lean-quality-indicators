@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace

namespace RingedSpaces.Modules.SheafInverseImage

universe v

variable {X Y : TopCat.{v}} (f : X ⟶ Y)

theorem ringIso_inv_hom_apply (S : Y.Sheaf CommRingCat.{v})
    (V : (Opens X)ᵒᵖ) (elem : (sheafifiedRing f S).obj.obj V) :
    (ringIso f S).hom.hom.app V ((ringIso f S).inv.hom.app V elem) = elem := by
  let e := (sheafToPresheaf (Opens.grothendieckTopology X) RingCat.{v}).mapIso
    (ringIso f S)
  have h := (e.app V).inv_hom_id
  change (ringIso f S).inv.hom.app V ≫ (ringIso f S).hom.hom.app V = 𝟙 _ at h
  simpa only [RingCat.comp_apply, RingCat.id_apply] using
    congrArg (fun map => map elem) h

end RingedSpaces.Modules.SheafInverseImage
end
