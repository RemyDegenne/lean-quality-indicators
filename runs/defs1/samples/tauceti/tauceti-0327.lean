public section

namespace TauCeti

namespace IntegralLattice

variable (n : ℕ)

variable {n}

variable (n)

section

variable [NeZero n]

/-- The final coordinate index `n - 1` of `Fin n`.  The Conway–Sloane vector class of the
checkerboard discriminant group is the standard vector at this index. -/
def checkerboardLastIndex : Fin n := ⟨n - 1, Nat.sub_lt (NeZero.pos n) Nat.one_pos⟩

end
end IntegralLattice
end TauCeti
end
