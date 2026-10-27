public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (indexType : Type u) [Fintype indexType] [DecidableEq indexType] (basis : Module.Basis indexType K V)

/-- The literal-order module is represented by the same group scheme after transport. -/
def sourceOrderedGeneralLinearPointsIso :
    sourceOrderedGeneralLinearFunctor K V ≅ generalLinearGroupPointsFunctor K indexType :=
  sourceOrderedGeneralLinearIso K V ≪≫ generalLinearModulePointsIso K V indexType basis

end AlgebraicGeometry
end
end
