public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (indexType : Type u) [Fintype indexType] [DecidableEq indexType] (basis : Module.Basis indexType K V)

/-- Coordinate evaluation of an automorphism, through its chosen-basis matrix. -/
@[expose] def generalLinearModuleCoordinateEval (R : Type u) [CommRing R] [Algebra K R]
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    CoordinateRing K indexType →ₐ[K] R :=
  evaluate (K := K) (generalLinearModuleMatrixEquiv K V indexType basis R f)

end AlgebraicGeometry
end
end
