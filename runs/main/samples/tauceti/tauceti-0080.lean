public section

open scoped WithZero

open MonoidWithZeroHom

namespace Valuation

section DivisionRing

variable {F : Type*} [DivisionRing F]

@[simp]
theorem ord_zpow (v : _root_.Valuation F ℤᵐ⁰) (f : F) (n : ℤ) :
    ord v (f ^ n) = n * ord v f := by
  simp [ord_def, map_zpow₀, WithZero.log_zpow, mul_neg]

end DivisionRing
end Valuation
end
