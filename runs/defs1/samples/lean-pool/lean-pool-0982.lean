@[expose] public section

open scoped Polynomial TensorProduct nonZeroDivisors

namespace BGS.HasseWeil

open BGS.CorvajaZannier

noncomputable section

variable (C S N : Type*) [Field C] [Field S] [Field N]
  [Algebra (RatFunc C) N] [Algebra C S]
  [FiniteDimensional C S] [IsGalois C S]

local instance constantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C (RatFunc C)))

local instance polynomialAlgebra : Algebra C[X] N :=
  RingHom.toAlgebra ((algebraMap (RatFunc C) N).comp
    (algebraMap C[X] (RatFunc C)))

local instance ratFuncCoefficientPolynomialAlgebra : Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance coefficientPolynomialModule : Module C[X] S[X] :=
  Algebra.toModule

local instance coefficientPolynomialFlat : Module.Flat C[X] S[X] := by
  let : Module.Flat C[X] (TensorProduct C C[X] S) := inferInstance
  exact Module.Flat.of_linearEquiv
    (Algebra.IsPushout.equiv C C[X] S S[X]).symm.toLinearEquiv

local instance constantPolynomialTower : IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' (by
    ext c
    change algebraMap (RatFunc C) N (algebraMap C (RatFunc C) c) =
      algebraMap (RatFunc C) N
        (algebraMap C[X] (RatFunc C) (Polynomial.C c))
    congr 1)

local instance targetPolynomialAlgebra :
    Algebra S[X] (ExactConstantExtension C N S) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N

section Exact

variable (hExact : algebraicClosure C N =
  (⊥ : IntermediateField C N))

/-- The algebra structure induced by the canonical copy of `S(X)`. -/
@[reducible] noncomputable def ratFuncExactConstantExtensionAlgebra :
    Algebra (RatFunc S) (ExactConstantExtension C N S) :=
  (ratFuncToExactConstantExtension C S N hExact).toAlgebra

end Exact
end
end BGS.HasseWeil
end
