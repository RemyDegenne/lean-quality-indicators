set_option autoImplicit false

noncomputable section

open scoped ModularForm MatrixGroups

namespace ModularCurve

theorem sharpIndex_def (ℓ : ℕ) : sharpIndex ℓ = Nat.gcd (ℓ - 1) 12 := rfl

end ModularCurve
end
