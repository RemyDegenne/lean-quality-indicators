@[expose] public section

open CategoryTheory Topology TopologicalSpace

namespace AlgebraicGeometry

universe u v

section Surjective

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes is surjective if the underlying map is. -/
@[mk_iff]
class Surjective : Prop where
  surj : Function.Surjective f

end Surjective
end AlgebraicGeometry
end
