public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry

/-- Affine schemes locally of finite type over a field. -/
abbrev lftAffineOver (K : Type u) [Field K] :=
  (locallyFiniteTypeMorphism.CostructuredArrow ⊤ Scheme.Spec (Spec (.of K)))

end AlgebraicGeometry
end
