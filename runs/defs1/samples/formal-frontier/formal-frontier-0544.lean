@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry

section General

variable (K : Type u) [CommRing K]

/-- Affine test morphisms whose opposite algebra map is faithfully flat. The target
algebra must itself be finitely generated over the base. -/
def faithfullyFlatTestMorphisms : MorphismProperty ((FGAlgCat.{u} K)ᵒᵖ) :=
  fun _ _ f ↦ f.unop.hom.hom.toRingHom.FaithfullyFlat

end General
end AlgebraicGeometry
end
