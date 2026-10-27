@[expose] public section

namespace RamanujanNagell

open Polynomial QuadraticAlgebra Algebra Nat
  UniqueFactorizationMonoid

/-- a(n) = θ^n + θ'^n, an integer recurrence. -/
def traceSeq : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => traceSeq (n + 1) - 2 * traceSeq n

end RamanujanNagell
end
