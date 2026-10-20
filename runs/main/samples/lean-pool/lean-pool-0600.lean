@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

open IsDedekindDomain

open scoped nonZeroDivisors Polynomial BigOperators

noncomputable section

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) coordinatePolePolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance coordinatePolePolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance coordinatePoleFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance coordinatePoleFiniteIntegralClosureIsIntegral :
    Algebra.IsIntegral K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra K[X] L

local instance coordinatePolePolynomialTorsionFreeTop :
    Module.IsTorsionFree K[X] L :=
  Module.IsTorsionFree.trans_faithfulSMul K[X] (RatFunc K) L

local instance coordinatePoleFiniteIntegralClosureIsTorsionFree :
    Module.IsTorsionFree K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree K[X] L

local instance coordinatePoleInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance coordinatePoleInfinityIntegralClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance coordinatePoleInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance coordinatePoleInfinityIntegralClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance coordinatePoleInfinityIntegralClosureIsDedekindDomain :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

local instance coordinatePoleInfinityIntegralClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
      (RatFuncInfinityIntegralClosure K L)

variable {K}

omit [Fintype K] [DecidableEq K] in
theorem finiteExtensionPoleDivisor_planeCurveFirstCoordinate_inr_positive
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI := finiteDimensional_planeCurveFunctionField_over_ratFunc
      hf hpartialSecond
    letI := separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    ∀ P : FiniteExtensionInfinityPlace K (PlaneCurveFunctionField f),
      0 < finiteExtensionPoleDivisor K (PlaneCurveFunctionField f)
        (planeCurveFunction f 0) (.inr P) := by
  classical
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let L := PlaneCurveFunctionField f
  let x : L := planeCurveFunction f 0
  let : Algebra (RatFunc K) L :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : FiniteDimensional (RatFunc K) L :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) L :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  change ∀ P : FiniteExtensionInfinityPlace K L,
    0 < finiteExtensionPoleDivisor K L x (.inr P)
  intro P
  have hnegative : finiteExtensionPrincipalDivisor K L x (.inr P) < 0 := by
    have hmapX : algebraMap (RatFunc K) L RatFunc.X = x := by
      dsimp only [x]
      exact planeCurveFirstCoordinateRatFuncAlgebra_X f hx
    rw [← hmapX]
    exact finiteExtensionPrincipalDivisor_algebraMap_X_inr_negative K L P
  rw [finiteExtensionPoleDivisor_apply, ite_eq_left hnegative]
  omega

end
end BGS.HasseWeil
end
