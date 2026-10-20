public section

open Function

variable {α β ι : Type*} {π : ι → Type*}

/-- An idempotent semiring is a semiring with the additional property that addition is idempotent.
-/
class IdemSemiring (α : Type*) extends Semiring α, SemilatticeSup α, OrderBot α where
  protected add_eq_sup (a b : α) : a + b = a ⊔ b := by intros; rfl

end
