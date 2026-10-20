public section

open CategoryTheory Opposite

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry

/-- The morphism property of being an open immersion, with its universe made explicit. -/
abbrev openImmersionMorphism : MorphismProperty Scheme.{u} :=
  @IsOpenImmersion

end AlgebraicGeometry
end
