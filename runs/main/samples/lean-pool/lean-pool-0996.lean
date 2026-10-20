@[expose] public section

namespace QuantumAlg

namespace PureState

noncomputable section

@[simp]
theorem invSqrt2_sq : invSqrt2 ^ 2 = (2 : ℂ)⁻¹ := by
  rw [sq, invSqrt2_mul_self]

end
end PureState
end QuantumAlg
end
