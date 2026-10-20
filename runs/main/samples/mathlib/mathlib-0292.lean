public section

variable (R : Type*) [CommRing R]

namespace EqualCharZero

theorem nonempty_algebraRat_iff :
    Nonempty (Algebra ℚ R) ↔ ∀ I : Ideal R, I ≠ ⊤ → CharZero (R ⧸ I) := by
  constructor
  · intro h_alg
    have h_alg' : Algebra ℚ R := h_alg.some
    apply of_algebraRat
  · intro h
    apply Nonempty.intro
    exact algebraRat h

end EqualCharZero
end
