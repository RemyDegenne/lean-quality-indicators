public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem z18_rho_mem_M (h : L41GPh14 t L S x₁ x₂ lam rho) : rho ∈ l41M t x₁ x₂ rho := by
  rw [h.qfacts.M_eq]
  exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
end
