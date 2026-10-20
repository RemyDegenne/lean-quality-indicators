public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (W : WeierstrassCurve R)

/-- **The Galois action on the coordinate ring of a base-changed Weierstrass curve.** An
`R`-automorphism `σ` of `A` acts on `A[W]` by applying `σ` to the coefficients and fixing the
classes of `x` and `y`: it is `AdjoinRoot.mapRingEquiv` along the coefficientwise `σ`, which fixes
the Weierstrass polynomial because `W` is defined over `R`. -/
noncomputable def coordinateRingGaloisAction :
    (A ≃ₐ[R] A) →* ((W⁄A).toAffine.CoordinateRing ≃+* (W⁄A).toAffine.CoordinateRing) where
  toFun σ := AdjoinRoot.mapRingEquiv (mapEquiv σ.toRingEquiv) (W⁄A).toAffine.polynomial
    (W⁄A).toAffine.polynomial
    (.of_eq (Affine.baseChange_polynomial (W := W) σ.toAlgHom).symm)
  map_one' := by
    apply RingEquiv.toRingHom_injective
    apply Affine.CoordinateRing.ringHom_ext
    · intro a
      rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply]
      simp [mapEquiv]
    · simp [mapEquiv]
    · simp
  map_mul' σ τ := by
    apply RingEquiv.toRingHom_injective
    apply Affine.CoordinateRing.ringHom_ext
    · intro a
      rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply]
      simp [mapEquiv]
    · simp [mapEquiv]
    · simp

end WeierstrassCurve
end
