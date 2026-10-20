@[expose] public section

open scoped Finset

namespace Nat

lemma mem_smoothNumbers_of_primeFactors_subset {m n : ℕ} (hm : m ≠ 0)
    (hp : m.primeFactors ⊆ Finset.range n) : m ∈ n.smoothNumbers :=
  smoothNumbers_eq_factoredNumbers n ▸ mem_factoredNumbers_of_primeFactors_subset hm hp

end Nat
end
