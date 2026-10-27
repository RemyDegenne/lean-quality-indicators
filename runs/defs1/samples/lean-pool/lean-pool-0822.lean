@[expose] public section

open scoped Polynomial TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier IsDedekindDomain

section TensorReciprocalNormalization

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [Algebra.IsSeparable (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance infinityBridgeDecidableEqBase : DecidableEq C := Classical.decEq C

local instance infinityBridgeDecidableEqConstants : DecidableEq S := Classical.decEq S

local instance infinityBridgeDecidableEqRatFuncBase : DecidableEq (RatFunc C) :=
  Classical.decEq (RatFunc C)

local instance infinityBridgeDecidableEqRatFuncConstants : DecidableEq (RatFunc S) :=
  Classical.decEq (RatFunc S)

local instance infinityBridgeBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance infinityBridgeBaseReciprocalPolynomialAlgebra : Algebra C[X] N :=
  ratFuncExtensionReciprocalPolynomialAlgebra C N

local instance infinityBridgeBaseConstantPolynomialTower :
    IsScalarTower C C[X] N := by
  exact IsScalarTower.of_algebraMap_eq' (by
    ext c
    change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
      algebraMap (RatFunc C) N
        (((reciprocalPolynomialRingHom C (Polynomial.C c) :
          RatFuncInfinityIntegers C) : RatFunc C))
    rw [reciprocalPolynomialRingHom_coe]
    simp)

local instance infinityBridgeOldNormalizationConstantAlgebra :
    Algebra C (integralClosure C[X] N) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (integralClosure C[X] N)).comp
      (algebraMap C C[X]))

local instance infinityBridgeOldNormalizationConstantPolynomialTower :
    IsScalarTower C C[X] (integralClosure C[X] N) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance infinityBridgeTensorPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] integralClosure C[X] N) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S
    (integralClosure C[X] N)

local instance infinityBridgeTensorConstantAlgebra :
    Algebra S (S ⊗[C] integralClosure C[X] N) :=
  Algebra.TensorProduct.leftAlgebra

local instance infinityBridgeTensorOldNormalizationAlgebra :
    Algebra (integralClosure C[X] N)
      (S ⊗[C] integralClosure C[X] N) :=
  Algebra.TensorProduct.rightAlgebra

/-- Contract a reciprocal tensor-normalization prime to the old reciprocal
normalization. -/
def exactConstantExtensionInfinityDownstairsIdeal
    (q : HeightOneSpectrum (S ⊗[C] integralClosure C[X] N)) :
    Ideal (integralClosure C[X] N) :=
  q.asIdeal.comap
    (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom

end TensorReciprocalNormalization
end
end BGS.HasseWeil
end
