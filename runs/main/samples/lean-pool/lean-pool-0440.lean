@[expose] public section

namespace Erdos137

open scoped BigOperators

open Finset

noncomputable section

lemma F_le_pow {k n : ℕ} (hk : 1 ≤ k) (hn : 1 ≤ n) : F k n ≤ (k * n) ^ k := by
  exact le_trans ( Finset.prod_le_prod fun _ _ => factor_le_mul hk hn ( Finset.mem_range.mp ‹_› ) )
    ( by norm_num )

end
end Erdos137
end
