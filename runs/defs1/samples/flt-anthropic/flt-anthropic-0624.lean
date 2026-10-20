namespace P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt

set_option autoImplicit false

namespace L2Aux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IsLocalRing

universe u

section Ker

variable {C K : Type*} [CommRing C] [Field K] (e : C →+* K) (A : ValuationSubring K)

noncomputable def toResidue (hA : ∀ c, e c ∈ A) : C →+* ResidueField A :=
  (residue A).comp (e.codRestrict A hA)

end Ker
end L2Aux
end P2MW.S_ModularCurve_FullLevel_exists_reads_resAut_smul_and_centred_iff_of_mem_closure_levelAutBar_twoChartIntegralModel
