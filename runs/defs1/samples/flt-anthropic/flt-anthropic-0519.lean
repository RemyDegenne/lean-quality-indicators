namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 3200000

set_option maxHeartbeats 51200000

namespace C3GlueKit

open IsLocalRing

section residueIso

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def comapIncl (A : ValuationSubring L) : ↥(A.comap (algebraMap K L)) →+* ↥A where
  toFun a := ⟨algebraMap K L a, a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

end residueIso
end C3GlueKit
end P2MW.S_ModularCurve_FullLevel_AuxLevel_isIntegrallyClosed_invariants_quotient_of_rigidChart_framed
