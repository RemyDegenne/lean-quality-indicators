namespace P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open IsDedekindDomain

p2m_reactivate

open IsDedekindDomain Polynomial

p2m_reactivate

open IsDedekindDomain Polynomial IsLocalRing

open scoped TensorProduct

p2m_reactivate

open IsDedekindDomain Polynomial IsLocalRing

p2m_reactivate

open IsDedekindDomain Polynomial IsLocalRing

p2m_reactivate

namespace AlgebraicCurve

p2m_open

namespace Place

p2m_open

section CenterIdeal

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

variable (A : Subalgebra K F) (hA : (A : Set F) ⊆ (v.toValuationSubring : Set F))

@[scoped simp] theorem coe_modelInclusion (a : A) :
    ((v.modelInclusion A hA a : v.toValuationSubring) : F) = (a : F) := rfl

end CenterIdeal
end Place
end AlgebraicCurve
end P2MW.S_AlgebraicCurve_exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver
