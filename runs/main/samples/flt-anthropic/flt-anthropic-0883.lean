namespace P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option maxHeartbeats 1600000

open scoped Pointwise

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v

namespace P2mKcFinQuot

section Setup

variable {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X)

@[reassoc (attr := simp)]
lemma ι_actMap (g : G) : copι ρ g ≫ actMap ρ = (ρ g).hom := Sigma.ι_desc _ _

end Setup
end P2mKcFinQuot
end P2MW.S_AlgebraicGeometry_Scheme_exists_quotient_of_finite_of_forall_exists_isAffineOpen_invariant
