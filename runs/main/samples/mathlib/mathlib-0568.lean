@[expose] public section

universe u

namespace Nat

theorem bit_ne_zero_iff {n : Nat} {b : Bool} : n.bit b ≠ 0 ↔ n = 0 → b = true := by
  simp

end Nat
end
