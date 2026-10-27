@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory Polynomial

open scoped CategoryTheory.MonObj

universe u v w t

namespace AlgebraicGeometry

/-- The affine scheme over `K` represented by `K[ZMod n]`. -/
abbrev rootsOfUnityScheme (K : Type u) [CommRing K] (n : ℕ) :
    Over (Spec (.of K)) :=
  (Spec (.of (rootsOfUnityCoordinateRing K n))).asOver (Spec (.of K))

end AlgebraicGeometry
end
end
