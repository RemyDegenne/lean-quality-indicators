public section

open scoped BigOperators

namespace CFSG.TwoRankLowerBound.Helpers

theorem root_supported_involution_pair_sum_eq_zero {G : Type*} [Group G] [Fintype G]
    (involution : G) (horder : orderOf involution = 2)
    (hunique : ∀ other : G, other ∈ Subgroup.centralizer ({involution} : Set G) →
      orderOf other = 2 → other = involution)
    (function : Subgroup.centralizer ({involution} : Set G) → ℂ)
    (hsupport : ∀ element : Subgroup.centralizer ({involution} : Set G),
      (element : G) ∉ cyclicRootSet involution → function element = 0)
    (involutions : Finset G) (hall : ∀ element ∈ involutions, orderOf element = 2) :
    ∑ left ∈ involutions, ∑ right ∈ involutions,
      inducedFunction (Subgroup.centralizer ({involution} : Set G)) function (left * right) = 0 := by
  apply Finset.sum_eq_zero
  intro left hleft
  apply Finset.sum_eq_zero
  intro right hright
  exact induced_root_supported_function_vanishes_on_involution_products involution horder
    hunique function hsupport left right (hall left hleft) (hall right hright)

end CFSG.TwoRankLowerBound.Helpers
end
