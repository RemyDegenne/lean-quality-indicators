@[expose] public section

open MeasureTheory Set

namespace QuadraticCarleson

/-- The explicit Calderón--Zygmund regularity constant of the low kernel at
height `B`. -/
noncomputable def lowKernelCZConstant (B : ℕ) : ℝ :=
  16 * lowKernelDerivativeConstant * (2 : ℝ) ^ (2 * B)

end QuadraticCarleson
end
