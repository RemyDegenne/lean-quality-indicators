namespace P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex

set_option autoImplicit false

universe u

open TensorProduct

namespace P2mMumfordKerModel

section Ext

variable {R : Type u} [CommRing R]

variable {M K : Type u} [AddCommGroup M] [Module R M] [AddCommGroup K] [Module R K]

variable (e : M →ₗ[R] K) {m : ℕ} (g : (Fin m → R) →ₗ[R] K)

def φ₀ : Kx e g →ₗ[R] M := LinearMap.fst R M (Fin m → R) ∘ₗ (Kx e g).subtype

end Ext
end P2mMumfordKerModel
end P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
