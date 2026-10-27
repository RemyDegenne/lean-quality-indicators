namespace P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed

set_option autoImplicit false

set_option maxHeartbeats 1600000

open scoped TensorProduct

universe u

namespace Ws47

namespace CB3

variable {K : Type u} [Field K]

section Frame

variable {A : Type u} [CommRing A] [Algebra K A] (Δ : A ⊗[K] A)

noncomputable def thetaₗ : Module.Dual K A →ₗ[K] A where
  toFun φ := Algebra.TensorProduct.lid K A (LinearMap.rTensor A φ Δ)
  map_add' φ ψ := by simp [LinearMap.rTensor_add]
  map_smul' c φ := by simp [LinearMap.rTensor_smul]

end Frame
end CB3
end Ws47
end P2MW.S_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed
