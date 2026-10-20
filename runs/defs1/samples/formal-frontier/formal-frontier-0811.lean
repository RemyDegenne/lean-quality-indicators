set_option autoImplicit false

set_option relaxedAutoImplicit false

namespace SignProduct

@[expose] public section

local instance : ContinuousSMul ℤˣ ℤ :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

/-- The action of the sign at one coordinate on the corresponding integer. -/
def coordinateAction (index : ℕ) (actor : SignGroup) (value : ℤ) : ℤ :=
  (actor index) • value

end
end SignProduct
