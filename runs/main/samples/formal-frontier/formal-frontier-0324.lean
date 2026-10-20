set_option autoImplicit false

set_option relaxedAutoImplicit false

namespace SignProduct

@[expose] public section

local instance : ContinuousSMul ℤˣ ℤ :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

@[simp] theorem flip_apply_self (index : ℕ) : flip index index = -1 := by
  simp [flip]

end
end SignProduct
