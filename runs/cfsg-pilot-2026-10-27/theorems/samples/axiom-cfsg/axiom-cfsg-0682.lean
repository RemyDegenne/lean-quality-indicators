public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap

open scoped commutatorElement

open CFSG.RankThree.Classical2 (orthDerived ProjOrthDerived)

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  (matrixProjectiveDerived matrixProjectiveProjection matrixDerived matrixDerivedScalars)

section HypCoord

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

variable {Q : QuadraticForm K (ι → K)} {a b : ι}

theorem perpPart_apply_left (hab : a ≠ b) (v : ι → K) : perpPart a b v a = 0 := by
  simp [perpPart, hab]

end HypCoord
end CFSG.SeitzReduction.OmegaPilot
end
