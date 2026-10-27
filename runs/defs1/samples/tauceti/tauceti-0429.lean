public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- The tensor product of the free sheaves of modules on `I` and on `I'` is the free sheaf of
modules on `I × I'`. The generator indexed by `(i, i')` corresponds to the tensor product of the
generators indexed by `i` and `i'` (`ιFree_freeTensorFreeIso_inv`). -/
def freeTensorFreeIso (I I' : Type u) :
    free (R := ringCatSheaf R) I ⊗ free I' ≅ free (I × I') :=
  (isColimitFreeCofan (R := ringCatSheaf R) (I × I')).coconePointsIsoOfNatIso
    (Cofan.IsColimit.prod
      (fun _ ↦ Cofan.mk (unit _ ⊗ free I') fun j ↦ unit _ ◁ ιFree j)
      (fun _ ↦ isColimitCofanMkObjOfIsColimit (tensorLeft (unit _)) _ _
        (isColimitFreeCofan (R := ringCatSheaf R) I'))
      (Cofan.mk (free I ⊗ free I') fun i ↦ ιFree i ▷ free I')
      (isColimitCofanMkObjOfIsColimit (tensorRight (free I')) _ _
        (isColimitFreeCofan (R := ringCatSheaf R) I)))
    (Discrete.natIso fun _ ↦ (λ_ (unit (ringCatSheaf R))).symm)
  |>.symm

end SheafOfModules
end
end TauCeti
end
