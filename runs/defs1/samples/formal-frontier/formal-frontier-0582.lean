@[expose] public section

noncomputable section

open scoped TensorProduct

namespace TensorProduct

/-- The algebraic tensor detector with values in real numbers modulo rational
numbers, induced by `rationalCircleBilinear`. -/
def rationalCircleDetector :
    ℚ ⊗[ℤ] AddCircle (1 : ℝ) →ₗ[ℤ] AddCircle.RationalQuotient :=
  TensorProduct.lift rationalCircleBilinear

end TensorProduct
end
end
