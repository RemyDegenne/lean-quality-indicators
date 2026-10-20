@[expose] public section

namespace Nat

theorem clog_le_of_le_pow {b x y : ℕ} (h : x ≤ b ^ y) : clog b x ≤ y := by
  rcases Nat.lt_or_ge 1 b with hb | hb
  · rwa [clog_le_iff_le_pow hb]
  · grind [clog_of_left_le_one]

end Nat
end
