public section

namespace CFSG.Quasithin.KGC31

theorem kgC31Ord_two_pow_mod_seven (f : ℕ) : 2 ^ f % 7 = 2 ^ (f % 3) % 7 := by
  have h3 : 2 ^ 3 ≡ 1 [MOD 7] := by decide
  have hpow : (2 ^ 3) ^ (f / 3) ≡ 1 [MOD 7] := by simpa using h3.pow (f / 3)
  have hf : 2 ^ f = (2 ^ 3) ^ (f / 3) * 2 ^ (f % 3) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h := hpow.mul_right (2 ^ (f % 3))
  rw [one_mul] at h
  rw [hf]
  exact h

end CFSG.Quasithin.KGC31
end
