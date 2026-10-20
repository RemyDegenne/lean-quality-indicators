public section

namespace TauCeti

universe v w

namespace ClassFunction

section Count

variable (k : Type) (G : Type v) [Semiring k] [Group G]

/-- **The square-root counting class function** `x ↦ #{g ∈ G : g² = x}`, with values in `k`.  It is
a class function by `TauCeti.card_squareRoot_conj`.

The count is a `Nat.card`, so on a group with an element having infinitely many square roots the
value there is `Nat.card`'s junk value `0` rather than a count; the pairing and counting formulas
below assume `Fintype G`. -/
noncomputable def squareRootCount : ClassFunction k G :=
  ⟨fun x => (Nat.card {g : G // g * g = x} : k),
    mem_iff.mpr fun x h => by rw [card_squareRoot_conj]⟩

end Count
end ClassFunction
end TauCeti
end
