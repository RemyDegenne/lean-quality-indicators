public section

namespace TauCeti

open Module

universe u v w

section Table

variable (k : Type u) (G : Type v) [Field k] [Group G] [Finite G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]

/-- **The character table of `G`**: the square matrix whose `(i, C)` entry is the value of the
`i`-th irreducible character of `G` on the conjugacy class `C`.

The rows are indexed by the chosen enumeration `TauCeti.finEquivIrreducibleCharacters` of the
irreducible characters and the columns by the conjugacy classes themselves, so the table is labelled
on its columns and determined up to a permutation of its rows. -/
noncomputable def characterTable :
    Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) k := fun i =>
  ClassFunction.toConjClasses (ClassFunction.ofCharacter (irreducibleRepresentation k i))

end Table
end TauCeti
end
