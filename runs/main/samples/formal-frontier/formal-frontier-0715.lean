@[expose] public section

namespace Nat

@[simp] theorem not_mem_primeSupportedIndices_zero (S : Set Nat.Primes) :
    0 ∉ primeSupportedIndices S := by
  simp [mem_primeSupportedIndices_iff]

end Nat
end
