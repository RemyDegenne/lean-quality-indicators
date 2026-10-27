@[expose] public section

variable {ι : Type*} {α : ι → Type*}

namespace DFinsupp

section Zero

variable [∀ i, Zero (α i)]

/-- `DFinsupp.Lex r s` is the lexicographic relation on `Π₀ i, α i`, where `ι` is ordered by `r`,
and `α i` is ordered by `s i`.

The type synonym `Lex (Π₀ i, α i)` has an order given by `DFinsupp.Lex (· < ·) (· < ·)`, whereas
`Colex (Π₀ i, α i)` has an order given by `DFinsupp.Lex (· > ·) (· < ·)`.
-/
protected def Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) (x y : Π₀ i, α i) : Prop :=
  Pi.Lex r (s _) x y

end Zero
end DFinsupp
end
