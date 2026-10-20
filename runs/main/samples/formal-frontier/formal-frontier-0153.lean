@[expose] public section

namespace Nat

@[simp] theorem mem_primeSupportedIndices_univ {n : ℕ} :
    n ∈ primeSupportedIndices (Set.univ : Set Nat.Primes) ↔ 0 < n := by
  simp [mem_primeSupportedIndices_iff]

end Nat
end
