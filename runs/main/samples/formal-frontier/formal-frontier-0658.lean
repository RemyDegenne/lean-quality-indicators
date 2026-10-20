set_option warningAsError true

@[expose] public section

namespace Bass

universe u v

variable {R : Type u} [Ring R]

@[simp]
theorem mem_principalRightIdeal {a y : R} :
    y ∈ principalRightIdeal a ↔ ∃ b : R, a * b = y :=
  Iff.rfl

end Bass
end
