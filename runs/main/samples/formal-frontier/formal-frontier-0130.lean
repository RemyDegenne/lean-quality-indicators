@[expose] public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing SpecialLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

variable (indexType : Type u) [Fintype indexType] [DecidableEq indexType]
  (basis : Module.Basis indexType K V)

variable (otherBasis thirdBasis : Module.Basis indexType K V)

omit [Module.Free K V] [Module.Finite K V] in
@[simp] theorem specialLinearModuleChangeBasis_apply (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) :
    specialLinearModuleChangeBasis K V indexType basis otherBasis R
        (specialLinearModuleMatrixEquiv K V indexType basis R f) =
      specialLinearModuleMatrixEquiv K V indexType otherBasis R f := by
  simp [specialLinearModuleChangeBasis]

end AlgebraicGeometry
end
end
