namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq

attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions

set_option autoImplicit false

set_option Elab.async false

set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

namespace FltWs24

namespace Asm

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section Site

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ

local notation "Fq" => modularFunctionFieldBar (1 * q)

local notation "Ck" => modularFunctionFieldC k 1

local notation "Plk" => Place k (modularFunctionFieldC k 1)

local notation "PlF" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))

local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

variable (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

open Classical in

noncomputable def D2 (E : Divisor Qb Fq) (Vfix : Finset Plk) (s : Plk → ℤ) (Sm : Finset k) (n₂ : k → ℕ) :
    Divisor k Ck :=
  Finsupp.mapDomain P.redSnd (P.sndPart E)
    + (∑ v ∈ Vfix, Finsupp.single (φ v) (Finsupp.mapDomain P.redFst E v + s v))
    + (∑ a ∈ Sm, Finsupp.single (frobNodePair q a).2 (n₂ a : ℤ))
    + Finsupp.single (P.redSnd (cuspZeroBar (1 * q)))
        (Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))))

end Site
end Asm
end FltWs24
end P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq
