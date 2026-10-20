@[expose] public section

open scoped TensorProduct

namespace CK

variable (k : Type*) [CommRing k]

variable [Algebra ℚ k]

omit [Algebra ℚ k] in
theorem _root_.CK.mul'_π :
    LinearMap.mul' k (Hab k) ∘ₗ TensorProduct.map (π k).toLinearMap (π k).toLinearMap
      = (π k).toLinearMap ∘ₗ LinearMap.mul' k (H k) := by
  apply TensorProduct.ext'
  simp_all

end CK
end
