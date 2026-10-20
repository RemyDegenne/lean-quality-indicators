set_option autoImplicit false

set_option relaxedAutoImplicit false

namespace SignProduct

@[expose] public section

local instance : ContinuousSMul ℤˣ ℤ :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

/-- The constant-one vector in the separately discrete product. -/
def discreteOneVector : DiscreteProduct :=
  discreteProductEquiv.symm oneVector

end
end SignProduct
