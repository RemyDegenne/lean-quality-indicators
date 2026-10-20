namespace P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit

set_option autoImplicit false

open scoped TensorProduct

open Function

universe u v w₁ w₂ w₃ w₄ w₅ w'

namespace Deformation

namespace FontaineExtStab

p2m_open

variable {𝓞 : Type u} [CommRing 𝓞] {p : ℕ} [Fact p.Prime]

variable {k : Type v} [CommRing k] [Algebra 𝓞 k]

noncomputable abbrev red {X : Type w₁} [CommRing X] [Algebra 𝓞 X] {Y : Type w'} [CommRing Y]
    [Algebra 𝓞 Y] (x : X →ₐ[𝓞] Y) : k ⊗[𝓞] X →ₐ[k] k ⊗[𝓞] Y :=
  Algebra.TensorProduct.map (AlgHom.id k k) x

end FontaineExtStab
end Deformation
end P2MW.S_Deformation_exists_algHom_baseChange_eq_of_faithfullyFlat_of_ker_eq_map_ker_counit
