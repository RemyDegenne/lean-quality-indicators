namespace P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace OrdProj

open ModularCurve

section JSide

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime]

theorem mem_Jtor {n : ℕ} (x : JH M H) : x ∈ Jtor M H p n ↔ ((p ^ n : ℕ) : ℤ) • x = 0 :=
  Submodule.mem_torsionBy_iff _ _

end JSide
end OrdProj
end P2MW.S_ModularCurve_exists_bialgHom_family_idempotent_inverse_U_of_cornerIdempotent_tateModule_jH
