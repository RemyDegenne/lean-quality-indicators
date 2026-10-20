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

omit [Module.Free K V] [Module.Finite K V] in
theorem specialLinearModuleMatrixEquiv_entry (R : Type u)
    [CommRing R] [Algebra K R]
    (f : SpecialLinearGroup R (SourceOrderTensor K V R)) (row column : indexType) :
    specialLinearModuleMatrixEquiv K V indexType basis R f row column =
      (generalLinearScalarBasis K V indexType basis R).repr
        (f ((generalLinearScalarBasis K V indexType basis R) column)) row := by
  exact Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq
    (generalLinearScalarBasis K V indexType basis R) f ▸
      LinearMap.toMatrix_apply _ _ _ _ _

end AlgebraicGeometry
end
end
