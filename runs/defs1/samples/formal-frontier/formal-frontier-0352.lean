public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

/-- A family of scheme morphisms is jointly scheme-theoretically dominant when the intersection
of their ideal-sheaf kernels is trivial. -/
def JointlySchemeTheoreticallyDominant (f : ∀ j, X j ⟶ Y) : Prop :=
  (⨅ j, (f j).ker) = ⊥

end AlgebraicGeometry
end
end
