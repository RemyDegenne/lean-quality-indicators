public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry

/-- The inclusion of affine locally-finite-type schemes into all locally-finite-type schemes over a
field. -/
@[implicit_reducible] noncomputable def lftAffineInclusion
    (K : Type u) [Field K] :
    lftAffineOver K ⥤ locallyFiniteTypeMorphism.Over ⊤ (Spec (.of K)) :=
  MorphismProperty.CostructuredArrow.toOver
    locallyFiniteTypeMorphism Scheme.Spec (Spec (.of K))

end AlgebraicGeometry
end
