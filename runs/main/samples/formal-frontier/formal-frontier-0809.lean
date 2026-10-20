public section

noncomputable section

open CategoryTheory TensorProduct GeneralLinearCoordinateRing

open scoped CategoryTheory.MonObj TensorProduct Matrix

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (V : Type u) [AddCommGroup V] [Module K V]
  (indexType : Type u) [Fintype indexType] [DecidableEq indexType] (basis : Module.Basis indexType K V)

theorem generalLinearModulePointsIso_apply_left (R : CommAlgCat K)
    (f : LinearMap.GeneralLinearGroup R (SourceOrderTensor K V R)) :
    ((generalLinearModulePointsIso K V indexType basis).hom.app R f).left =
      Spec.map (CommRingCat.ofHom
        (generalLinearModuleCoordinateEval K V indexType basis R f).toRingHom) := rfl

end AlgebraicGeometry
end
end
