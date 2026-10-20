@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

variable (K : Type u) [CommRing K]

section PowerKernel

theorem rootsOfUnityPowerSquare_isPullback_over (n : ℕ) :
    IsPullback (rootsOfUnityGroupSchemeInclusion K n).hom.hom
      (toUnit (rootsOfUnityScheme K n))
      ((𝟙 (multiplicativeGroupScheme K)) ^ n).hom.hom
      η[multiplicativeGroupUnderlyingScheme K] := by
  exact rootsOfUnityPowerSquare_over K n

end PowerKernel
end AlgebraicGeometry
end
end
