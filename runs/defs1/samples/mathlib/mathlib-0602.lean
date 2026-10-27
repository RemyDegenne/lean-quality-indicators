@[expose] public section

open Multiset

namespace Nat

namespace Partition

variable {n : ℕ} {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]

/-- The partition of exactly one part. -/
def indiscrete (n : ℕ) : Partition n := ofSums n {n} rfl

end Partition
end Nat
end
