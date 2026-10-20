public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {n : ℕ}

local notation "E" => ExactStructure.homologicalComplex (ExactStructure.split C)
  (ComplexShape.up (ZMod n))

local notation "hE" => ExactStructure.homologicalComplex_split_isFrobenius
  (C := C) (c := ComplexShape.up (ZMod n))
  (fun j => Exists.intro (j - 1) (by simp))
  (fun i => Exists.intro (i + 1) (by simp))

variable (C n)

@[simp]
theorem splitStableShiftObjIso_hom (X : CochainComplex C (ZMod n)) :
    letI := (hE).stableHasShift
    (splitStableShiftObjIso C n X).hom =
      (splitStableSuspensionIsoShift C n).inv.app X ≫
        (hE).stableShiftFunctorOneIso.inv.app ((E).projectiveStableFunctor.obj X) := (rfl)

end TauCeti.PeriodicComplex
end
