public section

open Function

variable {α β G M : Type*}

attribute [local simp] mul_assoc sub_eq_add_neg

section Group

variable [Group G] {a b c d : G} {n : ℤ}

@[to_additive] lemma mul_zpow_mul (a b : G) : ∀ n : ℤ, (a * b) ^ n * a = a * (b * a) ^ n
  | (n : ℕ) => by simp [mul_pow_mul]
  | .negSucc n => by simp [inv_mul_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq, mul_assoc, mul_pow_mul]

end Group
end
