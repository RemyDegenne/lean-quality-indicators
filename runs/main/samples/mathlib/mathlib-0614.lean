public section

open scoped Ring

variable {M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

section GroupWithZero

variable [GroupWithZero G₀]

theorem pow_inv_comm₀ (a : G₀) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left₀.pow_pow m n

end GroupWithZero
end
