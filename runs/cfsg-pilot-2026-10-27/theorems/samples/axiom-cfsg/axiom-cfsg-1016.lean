public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix

open scoped commutatorElement

set_option linter.unusedSectionVars false

section Commutator

variable {G : Type} [Group G] [Finite G]

theorem exists_moved_of_commutator_eq (F S : Subgroup G) (hS1 : S ≠ ⊥) (hSc : S = ⁅S, F⁆) :
    ∃ h ∈ F, ∃ x ∈ S, h * x * h⁻¹ ≠ x := by
  by_contra hno
  push Not at hno
  apply hS1
  rw [hSc, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun x hx h hh => ?_
  rw [Subgroup.mem_bot]
  have h1 := hno h hh x (hSc ▸ hx)
  calc x * h * x⁻¹ * h⁻¹ = x * (h * x⁻¹ * h⁻¹) := by group
    _ = x * (h * x * h⁻¹)⁻¹ := by group
    _ = 1 := by rw [h1, mul_inv_cancel]

end Commutator
end CFSG.RankThree.PartOne.K133C
end
