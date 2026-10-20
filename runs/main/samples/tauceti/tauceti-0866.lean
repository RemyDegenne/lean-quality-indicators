public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGRightModuleCat

universe uR uA uM

variable (R : Type uR) (A : Type uA) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

variable (R A)

@[simp]
theorem leftDegreeZeroEquivalence_counitIso_inv_app
    (M : ObjectProperty.FullSubcategory (IsConcentratedInDegreeZero
      (h := isDGAlgebra_zero (trivialGrading R Aᵐᵒᵖ)))) :
    (leftDegreeZeroEquivalence R A).counitIso.inv.app M =
      ObjectProperty.homMk ((degreeZeroIso M.obj M.property).inv ≫ (degreeZero R Aᵐᵒᵖ).map
        ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A).symm).counitIso.inv.app
          (forgetToRightModuleCat.obj M.obj))) := by
  simp only [leftDegreeZeroEquivalence, Equivalence.trans_counitIso]
  dsimp [degreeZeroEquivalence, degreeZeroToConcentrated]
  simp only [Category.id_comp, Category.comp_id, ObjectProperty.isoMk_inv]
  -- Composition in the induced full subcategory keeps the underlying composite.
  rfl

end TauCeti.DGRightModuleCat
end
end
