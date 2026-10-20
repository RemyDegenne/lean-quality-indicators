@[expose] public section

variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

variable {M}

namespace Con

section

variable [Mul M] [Mul N] [Mul P] {c d : Con M}

variable (c)

variable {c}

variable (c)

variable {c}

variable (c)

/-- The binary function on the quotient by a congruence relation `c` induced by a binary function
that is constant on `c`'s equivalence classes. -/
@[to_additive /-- The binary function on the quotient by a congruence relation `c`
induced by a binary function that is constant on `c`'s equivalence classes. -/]
protected def liftOn₂ {β} {c : Con M} (q r : c.Quotient) (f : M → M → β)
    (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β :=
  Quotient.liftOn₂' q r f h

end
end Con
end
