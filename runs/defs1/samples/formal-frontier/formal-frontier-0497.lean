set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The continuous quotient homomorphism from a finer open-normal stage to a coarser one. -/
def quotientTransitionHom (N M : OpenNormalSubgroup G) (hNM : N ≤ M) :
    (G ⧸ N.toSubgroup) →ₜ* (G ⧸ M.toSubgroup) := by
  letI : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology N.isOpen
  exact ⟨QuotientGroup.map N.toSubgroup M.toSubgroup (MonoidHom.id G)
    (by intro g hg; exact hNM hg), continuous_of_discreteTopology⟩

end ContinuousCohomology
end
