@[expose] public section

open Function OrderDual

variable {ι α β : Type*} {π : ι → Type*}

/-- The symmetric difference operator on a type with `⊔` and `\` is `(A \ B) ⊔ (B \ A)`. -/
@[to_dual
/-- The Heyting bi-implication is `(b ⇨ a) ⊓ (a ⇨ b)`. This generalizes equivalence of
propositions. -/]
def symmDiff [Max α] [SDiff α] (a b : α) : α :=
  a \ b ⊔ b \ a

end
