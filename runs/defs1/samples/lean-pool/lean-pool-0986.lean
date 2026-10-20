@[expose] public section

open scoped Polynomial TensorProduct BigOperators

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Fintype C] [Finite S]
  [DecidableEq C] [DecidableEq S]
  [DecidableEq (RatFunc C)] [DecidableEq (RatFunc S)]
  [Algebra (RatFunc C) N] [FiniteDimensional (RatFunc C) N]
  [IsGalois (RatFunc C) N]
  [Algebra C S] [FiniteDimensional C S] [IsGalois C S]

local instance finiteAverageRatFuncRationalFinitePlaceFintype :
    Fintype (RatFuncRationalFinitePlace C) := Fintype.ofFinite _

local instance finiteAverageBaseConstantAlgebra : Algebra C N :=
  bridgeBaseConstantAlgebra C N

local instance finiteAverageBaseConstantTower :
    IsScalarTower C (RatFunc C) N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finiteAverageTargetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  bridgeTargetPolynomialAlgebra C S N

local instance finiteAverageRatFuncClosureConstantAlgebra :
    Algebra C (RatFuncFiniteIntegralClosure C (RatFunc C)) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (RatFuncFiniteIntegralClosure C (RatFunc C))).comp
      (algebraMap C C[X]))

local instance finiteAverageRatFuncClosureConstantTower :
    IsScalarTower C C[X]
      (RatFuncFiniteIntegralClosure C (RatFunc C)) :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance finiteAverageRatFuncClosureModuleFinite :
    Module.Finite C[X] (RatFuncFiniteIntegralClosure C (RatFunc C)) :=
  Module.Finite.equiv
    (ratFuncFiniteBasePolynomialAlgEquivChart C).toLinearEquiv

/-- Degree-one finite places in the direct `C[X]` chart and in the generic
finite-extension place model of `C(X)` are canonically equivalent. -/
noncomputable def ratFuncRationalFinitePlaceEquivFiniteExtension :
    RatFuncRationalFinitePlace C ≃
      FiniteExtensionRationalFinitePlace C (RatFunc C) :=
  Equiv.subtypeEquiv (ratFuncFinitePlaceEquivFiniteExtension C) (by
    intro P
    rw [finiteExtensionPlaceDegree_ratFuncFinitePlaceEquivFiniteExtension])

end
end BGS.HasseWeil
end
