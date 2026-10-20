@[expose] public section

namespace MooreBound

open Module

namespace DegreeDiameter

variable {K : Type*} [DivisionRing K]

theorem one_le_evenEntryBlock {V : Type*} [AddCommGroup V] [Module K V]
    (k : ℕ) (e : V)
    (P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) :
    1 ≤ evenEntryBlock k e P := by
  rcases evenEntryBlock_spec k e P with h | h
  · exact h.1
  · omega

end DegreeDiameter
end MooreBound
end
