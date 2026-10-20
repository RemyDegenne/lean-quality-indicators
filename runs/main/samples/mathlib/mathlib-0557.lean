@[expose] public section

namespace NNRat

section Semifield

variable {K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

@[simp, norm_cast]
theorem floor_cast (x : ℚ≥0) : ⌊(x : K)⌋₊ = ⌊x⌋₊ :=
  (Nat.floor_eq_iff x.cast_nonneg).2 (mod_cast (Nat.floor_eq_iff x.cast_nonneg).1 (Eq.refl ⌊x⌋₊))

end Semifield
end NNRat
end
