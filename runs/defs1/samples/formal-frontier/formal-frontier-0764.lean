@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K] (D : Type u) [Fintype D]

/-- The affine cone is a product in the category of schemes over `Spec K`.
Its universal property includes every nonaffine test over-scheme. The proof uses
Mathlib's `algΓAlgSpecAdjunction` through `affineSpecHomOverEquiv` and the
universal evaluation map `MvPolynomial.aeval`. -/
def additiveGroupAffineProductFan_isLimit :
    Limits.IsLimit (additiveGroupAffineProductFan K D) := by
  classical
  refine Limits.Fan.IsLimit.mk _ (fun s ↦
    (affineSpecHomOverEquiv K s.pt (MvPolynomial D K)).symm
      (MvPolynomial.aeval (fun d ↦ additiveGroupHomOverEquiv K s.pt (s.proj d)))) ?_ ?_
  · intro s d
    apply (additiveGroupHomOverEquiv K s.pt).injective
    change additiveGroupGlobalCoordinate K s.pt
      ((affineSpecHomOverEquiv K s.pt (MvPolynomial D K)).symm
        (MvPolynomial.aeval (fun d ↦ additiveGroupHomOverEquiv K s.pt (s.proj d))) ≫
          additiveGroupAffineProductProjection K D d) =
        additiveGroupGlobalCoordinate K s.pt (s.proj d)
    erw [additiveGroupAffineProductProjection_globalCoordinate]
    simp only [additiveGroupAffineProductGlobalCoordinate,
      additiveGroupGlobalCoordinate, Equiv.apply_symm_apply, MvPolynomial.aeval_X]
  · intro s m hm
    apply (affineSpecHomOverEquiv K s.pt (MvPolynomial D K)).injective
    apply MvPolynomial.algHom_ext
    intro d
    have hfac : m ≫ additiveGroupAffineProductProjection K D d = s.proj d := hm d
    have hcoord := congrArg (additiveGroupHomOverEquiv K s.pt) hfac
    change additiveGroupGlobalCoordinate K s.pt
      (m ≫ additiveGroupAffineProductProjection K D d) =
        additiveGroupGlobalCoordinate K s.pt (s.proj d) at hcoord
    erw [additiveGroupAffineProductProjection_globalCoordinate] at hcoord
    simpa only [additiveGroupAffineProductGlobalCoordinate,
      additiveGroupGlobalCoordinate, Equiv.apply_symm_apply, MvPolynomial.aeval_X] using hcoord

end AlgebraicGeometry
end
end
