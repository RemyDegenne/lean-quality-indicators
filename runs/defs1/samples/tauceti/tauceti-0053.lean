public section

open Bundle Manifold VectorField

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- The differential of a smooth Riemannian isometry at a point, as a linear isometric
equivalence of tangent spaces. Its underlying linear equivalence is Mathlib's
`Diffeomorph.mfderivToContinuousLinearEquiv`, bundled isometrically with Mathlib's
`LinearEquiv.isometryOfInner`. -/
def mfderivToLinearIsometryEquiv (Φ : RiemannianIsometry I J M N) (x : M) :
    TangentSpace I x ≃ₗᵢ[ℝ] TangentSpace J (Φ x) :=
  LinearEquiv.isometryOfInner
    (Φ.toDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    fun v w ↦ by
      have he : (Φ.toDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x :
          TangentSpace I x →L[ℝ] TangentSpace J (Φ x)) =
          mfderiv I J Φ.toDiffeomorph x :=
        Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ.toDiffeomorph (by simp)
      exact (congrArg₂ (inner ℝ) (DFunLike.congr_fun he v) (DFunLike.congr_fun he w)).trans
        (Φ.inner_mfderiv x v w)

end TauCeti.RiemannianIsometry
end
end
