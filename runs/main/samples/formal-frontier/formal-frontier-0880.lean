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
theorem specialLinearModuleChangeBasis_toGL (R : Type u)
    [CommRing R] [Algebra K R] (f : Matrix.SpecialLinearGroup indexType R) :
    Matrix.SpecialLinearGroup.toGL
        (specialLinearModuleChangeBasis K V indexType basis otherBasis R f) =
      generalLinearModuleChangeBasis K V indexType basis otherBasis R
        (Matrix.SpecialLinearGroup.toGL f) := by
  obtain ⟨h, rfl⟩ := (specialLinearModuleMatrixEquiv K V indexType basis R).surjective f
  rw [specialLinearModuleChangeBasis_apply,
    specialLinearModuleMatrixEquiv_toGL,
    specialLinearModuleMatrixEquiv_toGL]
  exact (generalLinearModuleChangeBasis_apply K V indexType basis otherBasis R
    h.toGeneralLinearGroup).symm

end AlgebraicGeometry
end
end
