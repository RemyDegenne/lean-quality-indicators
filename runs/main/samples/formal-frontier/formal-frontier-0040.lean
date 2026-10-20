set_option warningAsError true

@[expose] public section

namespace TwoSidedIdeal

universe u

variable {R : Type u} [Ring R]

@[simp] theorem isNil_bot : (⊥ : TwoSidedIdeal R).IsNil := by
  intro x hx
  have hx0 : x = 0 := by simpa using hx
  subst x
  exact IsNilpotent.zero

end TwoSidedIdeal
end
