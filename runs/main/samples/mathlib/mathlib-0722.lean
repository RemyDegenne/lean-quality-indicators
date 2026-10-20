public section

namespace Int

variable {m n : ℤ}

@[simp, norm_cast] lemma odd_coe_nat (n : ℕ) : Odd (n : ℤ) ↔ Odd n := by grind

end Int
end
