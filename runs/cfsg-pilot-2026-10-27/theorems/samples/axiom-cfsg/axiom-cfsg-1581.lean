public section

namespace CFSG.OrderReductions.ThompsonGrowthTrap

open CFSG.OrderReductions.ThompsonCenter CFSG.OrderReductions.ActionPrimeCore CFSG.OrderReductions.PrimeCore

open CFSG.OrderReductions.PrimeQuotientFrattini CFSG.OrderReductions.ThompsonGrowthCore

attribute [local instance] commutatorElement

theorem internal_commutator_central_of_ambient {group : Type*} [Group group]
    (subgroup : Subgroup group)
    (central : ⁅subgroup, subgroup⁆ ≤ Subgroup.centralizer (subgroup : Set group)) :
    commutator subgroup ≤ Subgroup.center subgroup := by
  intro element element_mem
  have image_mem : element.val ∈ ⁅subgroup, subgroup⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact Subgroup.mem_map.mpr ⟨element, element_mem, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro other
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (central image_mem) other.val other.property)

end CFSG.OrderReductions.ThompsonGrowthTrap
end
