public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (indexType : Type u) [Fintype indexType] [DecidableEq indexType] (basis : Module.Basis indexType K V)

variable (otherBasis thirdBasis : Module.Basis indexType K V)

theorem generalLinearModulePointsIso_changeBasis (R : CommAlgCat K)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    (generalLinearModulePointsIso K V indexType otherBasis).hom.app R f =
      (generalLinearGroupPointsIso K indexType).hom.app R
        (generalLinearModuleChangeBasis K V indexType basis otherBasis R
          (generalLinearModuleMatrixEquiv K V indexType basis R f)) := by
  simp only [generalLinearModulePointsIso, generalLinearModuleChangeBasis,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

end AlgebraicGeometry
end
end
