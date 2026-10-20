namespace P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf

attribute [-instance] FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane hiding I

open MeasureTheory Filter Complex Set

open scoped MatrixGroups Topology Real ComplexConjugate ModularForm

namespace ModularCurve

namespace DivisorTerm

p2m_open

section Primitives

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

def Eg (g : CuspForm Γ 2) (z : ℂ) : ℂ :=
  ModularCurve.periodAlongOf Γ UpperHalfPlane.I (ofComplex z) g

end Primitives
end DivisorTerm
end ModularCurve
end
end P2MW.S_ModularCurve_exists_invariant_localModel_tendsto_integral_dbarLogDeriv_smoothedFundamental_periodAlongOf
