namespace P2MW.S_StructureConstants_assoc_and_unit_and_comm_intCast_of_linearIndependent

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace StructureConstantsSol

variable {A : Type*} [Ring A] {K : ℕ} (u : Fin K → A) (c : Fin K → Fin K → Fin K → ℤ) (c₁ : Fin K → ℤ)

section AnyRing

variable (R : Type*) [CommRing R]

theorem cst_eq_sum_right (a b : Fin K → R) (s : Fin K) :
    cst c R a b s = ∑ l, b l * ∑ k, a k * (c k l s : R) := by
  rw [cst_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end AnyRing
end StructureConstantsSol
end
end P2MW.S_StructureConstants_assoc_and_unit_and_comm_intCast_of_linearIndependent
