@[expose] public section

namespace QuantumAlg

universe u

namespace Simon

variable {n : ℕ} {α : Type u}

theorem satisfiesEquations_add {samples : Finset (BitVec n)} {a b : BitVec n}
    (ha : SatisfiesEquations samples a) (hb : SatisfiesEquations samples b) :
    SatisfiesEquations samples (a + b) := by
  intro y hy
  rw [SatisfiesEquation, Orthogonal, dot_add_right, ha y hy, hb y hy]
  simp

end Simon
end QuantumAlg
end
