namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero

attribute [-instance] MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup HopfAlgebra.HopfIdealQuotient.instIsCocomm HopfAlgebra.HopfIdealQuotient.instBialgebra HopfAlgebra.HopfIdealQuotient.instHopfAlgebra Ideal.isHopfIdeal_bot HopfAlgebra.flat_quotient_bot HopfAlgebra.finiteType_quotient instTopologicallyFGOfFiniteType CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup CerednikDrinfeld.LubinTate.instIsCommMap CerednikDrinfeld.LubinTate.instFintypeGaloisFieldTwo CerednikDrinfeld.LubinTate.sigma_isComm CerednikDrinfeld.LubinTate.sigmaBar_isComm CerednikDrinfeld.BoxBasisLemma.instDecidableInBox CerednikDrinfeld.Standard.law_isComm MvFormalGroup.CartierModule.instModulePadicInt MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra

attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace InjK0

section Base

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]

local notation "k₀" => WittVector p k ⧸ pIdeal p (WittVector p k)

local notation "qk" => Ideal.Quotient.mk (pIdeal p (WittVector p k))

abbrev ψ_ (B : Type) [CommRing B] [Algebra k₀ B] : WittVector p k →+* B := (algebraMap k₀ B).comp qk

end Base
end InjK0
end
end P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
