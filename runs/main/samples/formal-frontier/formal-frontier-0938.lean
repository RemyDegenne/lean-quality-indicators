@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Nat

namespace PowerIndex

variable {S : Set Nat.Primes}

theorem mul_le_right (n d : PowerIndex S) : n * d ≤ d := by
  exact ⟨n.val, by simp only [mul_val, mul_comm]⟩

end PowerIndex
end Nat
end
