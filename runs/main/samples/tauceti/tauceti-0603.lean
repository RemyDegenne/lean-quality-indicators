public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [HasBinaryBiproducts C] [EssentiallySmall.{w} C]

omit [HasZeroObject C] in
@[simp]
lemma objectCode_biprod (X Y : C) : objectCode (X ⊞ Y) = objectCode X + objectCode Y :=
  (objectCode_biprod_congr (Function.surjInv_eq objectCode_surjective (objectCode X)).symm
    (Function.surjInv_eq objectCode_surjective (objectCode Y)).symm).trans
      (ObjectCode.add_def _ _).symm

end TauCeti
end
