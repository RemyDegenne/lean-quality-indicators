namespace P2MW.S_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff

set_option autoImplicit false

open scoped TensorProduct

universe v

namespace RingHom

namespace CasimirLiftAux

p2m_open

variable {R : Type v} [Ring R]

def IsCasimir (c : R ⊗[ℤ] R) : Prop :=
  ∀ x : R, (x ⊗ₜ[ℤ] (1 : R)) * c = c * ((1 : R) ⊗ₜ[ℤ] x)

end CasimirLiftAux
end RingHom
end P2MW.S_RingHom_exists_casimir_map_mul_eq_one_of_surjective_of_forall_map_eq_zero_iff
