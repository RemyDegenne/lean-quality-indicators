namespace P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField

set_option autoImplicit false

set_option linter.unusedSectionVars false

open Polynomial

open scoped MatrixGroups

namespace ModularCurve p2m_export "ModularCurve" "intSeriesC intFormRatiosC x1FunctionField jNum constantCoeff_jNum jq coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange mem_laurentBaseChange_iff" namespace GaussPres end ModularCurve.GaussPres

p2m_open_scoped "ModularCurve" in

namespace ModularCurve

namespace GaussPres

p2m_open

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  {L : Type*} [Field L] [Algebra A L] [IsFractionRing A L]

def IsPres (f : LaurentSeries L) (x y : PowerSeries A) : Prop := f * toLS A L y = toLS A L x

end GaussPres
end ModularCurve
end ModularCurve
end P2MW.S_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
