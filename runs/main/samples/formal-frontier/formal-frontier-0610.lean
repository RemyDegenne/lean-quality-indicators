@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Nat

namespace PowerIndex

variable {S : Set Nat.Primes}

@[simp] theorem ofSupported_val (n : ℕ) (hn : n ∈ primeSupportedIndices S) :
    (ofSupported n hn).val = n := rfl

end PowerIndex
end Nat
end
