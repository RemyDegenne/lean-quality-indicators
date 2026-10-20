public section

variable {ι α : Type*} {R : ι → Type*}

namespace Pi

section

variable [∀ i, Mul (R i)]

@[to_additive (attr := simp)]
theorem isRightRegular_iff {a : ∀ i, R i} : IsRightRegular a ↔ ∀ i, IsRightRegular (a i) :=
  have (i : _) : Nonempty (R i) := ⟨a i⟩; .symm Pi.map_injective.symm

end
end Pi
end
