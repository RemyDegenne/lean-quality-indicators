@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

section PowerKernel

theorem rootsOfUnitySchemeKernel_universal (n : ℕ)
    (T : Over (Spec (.of K))) (f : T ⟶ multiplicativeGroupUnderlyingScheme K)
    (hf : f ≫ ((𝟙 (multiplicativeGroupScheme K)) ^ n).hom.hom =
      toUnit T ≫ η[multiplicativeGroupUnderlyingScheme K]) :
    ∃! lift : T ⟶ rootsOfUnityScheme K n,
      lift ≫ (rootsOfUnityGroupSchemeInclusion K n).hom.hom = f := by
  let square := rootsOfUnityPowerSquare_isPullback_over K n
  refine ⟨square.lift f (toUnit T) hf, square.lift_fst _ _ _, ?_⟩
  intro candidate hcandidate
  apply square.hom_ext
  · exact hcandidate.trans (square.lift_fst _ _ _).symm
  · exact toUnit_unique _ _

end PowerKernel
end AlgebraicGeometry
end
end
