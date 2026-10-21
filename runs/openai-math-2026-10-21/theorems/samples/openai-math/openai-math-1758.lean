namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

@[simp] theorem actualWeightField_apply (θ c : ℕ → ℝ) (x : Base) (k : ℤ) :
    actualWeightField θ c x k = (weight θ c (rotationIterate θ k x) : ℂ) := rfl

end Invariant233.ProductModel
end
end OAI
