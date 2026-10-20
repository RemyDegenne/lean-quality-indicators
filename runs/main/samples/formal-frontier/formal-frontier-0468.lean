set_option autoImplicit false

set_option relaxedAutoImplicit false

namespace SignProduct

@[expose] public section

local instance : ContinuousSMul ℤˣ ℤ :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

theorem coordinateAction_continuous (index : ℕ) :
    Continuous (fun pair : SignGroup × ℤ =>
      coordinateAction index pair.1 pair.2) := by
  exact ((continuous_apply index).comp continuous_fst).smul continuous_snd

end
end SignProduct
