namespace P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct

open TensorProduct LinearMap

noncomputable section

set_option synthInstance.maxHeartbeats 800000

namespace FlatDescentFG

universe u v w

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Transition

variable {R₀ : Type*} [CommRing R₀] (B₀ : Type*) [CommRing B₀] [Algebra R₀ B₀]
  (p₀ : Ideal R₀)

variable {A : Type*} [CommRing A] [Algebra R₀ A] {A' : Type*} [CommRing A'] [Algebra R₀ A']
  {A'' : Type*} [CommRing A''] [Algebra R₀ A'']

def δ (h : A →ₐ[R₀] A') : A ⊗[R₀] B₀ →ₐ[R₀] A' ⊗[R₀] B₀ :=
  Algebra.TensorProduct.map h (AlgHom.id R₀ B₀)

end Transition
end FlatDescentFG
end
end P2MW.S_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct
