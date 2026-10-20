public section

noncomputable section

open TensorProduct

open scoped TensorProduct

namespace AlgebraicGeometry

universe u v w w₁ w₂

variable (K : Type u) [CommRing K] (V : Type v) [AddCommGroup V] [Module K V]
  (R : Type w) [CommRing R] [Algebra K R]

theorem sourceOrderTensor_smul_tmul (v : V) (r s : R) :
    r • sourceOrderTensorEquiv K V R (v ⊗ₜ[K] s) =
      sourceOrderTensorEquiv K V R (v ⊗ₜ[K] (r * s)) := by
  simp [sourceOrderTensorEquiv, TensorProduct.smul_tmul']

end AlgebraicGeometry
end
end
