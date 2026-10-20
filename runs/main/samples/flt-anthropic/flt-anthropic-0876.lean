namespace P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

p2m_open

namespace CerednikDrinfeld

namespace FormalOmega

namespace LevelAux

p2m_open

open TensorProduct

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}

variable {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']

variable {R : Type} [CommRing R] [Algebra 𝒪 R]

theorem red_zero_eq_id (π : 𝒪) : red (R := R) π 0 = AlgHom.id 𝒪 (modPow π R 0) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro r
  rfl

end LevelAux
end FormalOmega
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_FormalOmega_AdicPoint_exists_toOmega_eq_of_mem_affinoid_zero_or_lt
