@[expose] public section

open scoped Relator

namespace Filter

variable {α β γ δ : Type*} {l : Filter α} {f g h : α → β}

namespace Germ

/-- Given a germ `f : Germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
def liftOn {γ : Sort*} (f : Germ l β) (F : (α → β) → γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F) :
    γ :=
  Quotient.liftOn' f F hF

end Germ
end Filter
end
