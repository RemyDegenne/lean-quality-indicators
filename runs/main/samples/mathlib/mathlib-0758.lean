@[expose] public section

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

open scoped Ring

namespace Units

variable [GroupWithZero G₀]

theorem mul_inv' (u : G₀ˣ) : u * (u : G₀)⁻¹ = 1 :=
  mul_inv_cancel₀ u.ne_zero

end Units
end
