set_option autoImplicit false

set_option relaxedAutoImplicit false

namespace SignProduct

@[expose] public section

local instance : ContinuousSMul ℤˣ ℤ :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

@[simp] theorem discrete_add (left right : DiscreteProduct) :
    discreteProductEquiv (left + right) =
      discreteProductEquiv left + discreteProductEquiv right :=
  discreteProductAddEquiv.map_add left right

end
end SignProduct
