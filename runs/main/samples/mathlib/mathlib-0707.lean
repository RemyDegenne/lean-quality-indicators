@[expose] public section

namespace Nat

lemma log_two_bit {b n} (hn : n ≠ 0) : Nat.log 2 (n.bit b) = Nat.log 2 n + 1 := by
  rw [← log_div_mul_self, bit_div_two, log_mul_base Nat.one_lt_two hn]

end Nat
end
