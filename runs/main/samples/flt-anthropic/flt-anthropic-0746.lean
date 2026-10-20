namespace P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 3200000

set_option maxHeartbeats 0

attribute [local instance 10000] SubalgebraClass.toAlgebra Algebra.toSMul Algebra.toModule

attribute [local instance 10001] AdicCompletion.instAlgebra

namespace S3GlueKit

open IsLocalRing

section image

variable {K L : Type*} [Field K] [Field L]

theorem mem_imS_iff {e : K ≃+* L} {O : Subring K} {y : L} : y ∈ imS e O ↔ e.symm y ∈ O := by
  unfold imS
  rw [Subring.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    show e.symm (e x) ∈ O
    rw [e.symm_apply_apply]; exact hx
  · intro h; exact ⟨e.symm y, h, e.apply_symm_apply y⟩

end image
end S3GlueKit
end P2MW.S_ModularCurve_FullLevel_Diamond_exists_moduliHasse_commonChart_nodes_igusaSep_levelField_of_nodes_fixedField_of_algEquiv_of_eq_two_of_dvd
