@[expose] public section

open scoped nonZeroDivisors Polynomial BigOperators

open IsDedekindDomain

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance (priority := 10) zeroCountingPolynomialAlgebra :
    Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance zeroCountingPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance zeroCountingFiniteIntegralClosureModuleFinite :
    Module.Finite K[X] (RatFuncFiniteIntegralClosure K L) :=
  Module.IsNoetherian.finite K[X] (RatFuncFiniteIntegralClosure K L)

local instance zeroCountingInfinityIntegralClosureModuleFinite :
    Module.Finite (RatFuncInfinityIntegers K)
      (RatFuncInfinityIntegralClosure K L) :=
  IsIntegralClosure.finite (RatFuncInfinityIntegers K) (RatFunc K) L
    (RatFuncInfinityIntegralClosure K L)

omit [DecidableEq K] in
@[simp] theorem mem_finiteExtensionZeroPlaces_iff
    (x : L) (v : FiniteExtensionPlace K L) :
    v ∈ finiteExtensionZeroPlaces K L x ↔
      0 < finiteExtensionPrincipalDivisor K L x v := by
  simp only [finiteExtensionZeroPlaces, Finset.mem_filter,
    Finsupp.mem_support_iff]
  omega

end
end BGS.HasseWeil
end
