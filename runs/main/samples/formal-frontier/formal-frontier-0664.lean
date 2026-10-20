set_option autoImplicit false

set_option relaxedAutoImplicit false

namespace SignProduct

@[expose] public section

local instance : ContinuousSMul ℤˣ ℤ :=
  ⟨continuous_prod_of_discrete_left.mpr continuous_const_smul⟩

theorem signGroup_topological :
    IsTopologicalGroup SignGroup ∧ CompactSpace SignGroup ∧
      T2Space SignGroup ∧ TotallyDisconnectedSpace SignGroup := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end
end SignProduct
