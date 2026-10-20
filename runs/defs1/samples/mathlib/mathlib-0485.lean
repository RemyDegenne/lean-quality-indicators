@[expose] public section

noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u u₁

variable {C : Type u₁} [Category.{v} C]

section

variable {X : Scheme.{u}} (U : X.Opens)

namespace Scheme.Opens

/-- The restriction of a scheme to an open subset. -/
def ι : ↑U ⟶ X := X.ofRestrict _

end Scheme.Opens
end
end AlgebraicGeometry
end
end
