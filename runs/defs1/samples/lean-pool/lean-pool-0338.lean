@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier

open IsDedekindDomain Multiplicative WithZero

open scoped Polynomial

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance riemannRochConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance riemannRochConstantRatFuncTower : IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance (priority := 10) riemannRochPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance riemannRochPolynomialRatFuncTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance riemannRochConstantPolynomialTower : IsScalarTower K K[X] L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance riemannRochInfinityBaseConstantAlgebra :
    Algebra K (RatFuncInfinityIntegers K) :=
  (ratFuncInfinityConstantRingHom K).toAlgebra

local instance riemannRochInfinityClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance riemannRochInfinityClosureIsIntegral :
    Algebra.IsIntegral (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isIntegral_algebra (RatFuncInfinityIntegers K) L

local instance riemannRochInfinityBaseTorsionFreeTop :
    Module.IsTorsionFree (RatFuncInfinityIntegers K) L :=
  Module.IsTorsionFree.trans_faithfulSMul
    (RatFuncInfinityIntegers K) (RatFunc K) L

local instance riemannRochInfinityClosureIsTorsionFree :
    Module.IsTorsionFree (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isTorsionFree (RatFuncInfinityIntegers K) L

local instance riemannRochInfinityClosureIsDedekind :
    IsDedekindDomain (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.isDedekindDomain
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance riemannRochInfinityClosureIsFractionRing :
    IsFractionRing (RatFuncInfinityIntegralClosure K L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

local instance riemannRochInfinityClosureConstantAlgebra :
    Algebra K (RatFuncInfinityIntegralClosure K L) :=
  RingHom.toAlgebra
    ((algebraMap (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L)).comp
      (algebraMap K (RatFuncInfinityIntegers K)))

local instance riemannRochInfinityClosureConstantTower :
    IsScalarTower K (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The residue-field equivalence for the finite quotient in Riemann–Roch. -/
noncomputable def finiteExtensionFiniteQuotientResidueAlgEquiv
    (q : FiniteExtensionFinitePlace K L) :
    (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal) ≃ₐ[K]
      q.asIdeal.ResidueField := by
  letI : q.asIdeal.IsMaximal := q.isPrime.isMaximal q.ne_bot
  exact AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom K
      (RatFuncFiniteIntegralClosure K L ⧸ q.asIdeal)
      q.asIdeal.ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField q.asIdeal)

end
end BGS.HasseWeil
end
