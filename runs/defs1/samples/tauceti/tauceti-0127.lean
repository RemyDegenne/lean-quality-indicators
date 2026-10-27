public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti.DGRightModuleCat

universe uR uA uM

variable (R : Type uR) (A : Type uA) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

variable (R A)

/-- Ordinary left modules are equivalent to right DG modules over the opposite algebra
concentrated in degree zero. -/
-- As for `degreeZeroEquivalence`, exposure is needed to type-check the public pointwise
-- statements and counit component equations with the original modules as their carriers.
@[expose]
def leftDegreeZeroEquivalence : ModuleCat.{uM} A ≌
    ObjectProperty.FullSubcategory (IsConcentratedInDegreeZero
      (h := isDGAlgebra_zero (trivialGrading R Aᵐᵒᵖ))) :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A).symm).trans
    (degreeZeroEquivalence R Aᵐᵒᵖ)

end TauCeti.DGRightModuleCat
end
end
