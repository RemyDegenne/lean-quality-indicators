namespace P2MW.S_ModularCurve_FullLevel_exists_levelAut_smul_mem_igusaDisc_of_forall_not_inTube_of_eq_three_of_dvd

attribute [-instance] ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex

p2m_reactivate

p2m_reactivate

section Inlined_w1_W1c_spec

set_option autoImplicit false

p2m_open

open scoped MatrixGroups

noncomputable section

namespace ModularCurve

namespace FullLevel

namespace W1c

p2m_open

section Spec

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (A : ValuationSubring (AlgebraicClosure ℚ))

set_option synthInstance.maxHeartbeats 1600000 in

def LevelAuts : Subgroup ((fieldBar q M') ≃ₐ[(AlgebraicClosure ℚ)] (fieldBar q M')) :=
  Subgroup.closure {τ | ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ}

end Spec
end W1c
end FullLevel
end ModularCurve
end
end Inlined_w1_W1c_spec
end P2MW.S_ModularCurve_FullLevel_exists_levelAut_smul_mem_igusaDisc_of_forall_not_inTube_of_eq_three_of_dvd
