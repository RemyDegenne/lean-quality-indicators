public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open TopologicalSpace

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {G : Scheme.{u}}

/-- The type of `K`-rational points over `Spec K`. It inherits its group
structure when `Over.mk f` is a group object. -/
abbrev groupSchemePoints (f : G ⟶ Spec (.of K)) : Type u :=
  𝟙_ (Over (Spec (.of K))) ⟶ Over.mk f

end AlgebraicGeometry
end
end
