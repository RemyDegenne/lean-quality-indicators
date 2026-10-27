namespace P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant

set_option autoImplicit false

p2m_open

namespace IharaTower

namespace ResidualInjectivity

p2m_open

section Reduction

variable {𝒪 : Type} [CommRing 𝒪] (ϖ : 𝒪) (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def red : H1 M H 𝒪 →+ H1 M H (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) :=
  AddMonoidHom.compHom ((Ideal.Quotient.mk (Ideal.span ({ϖ} : Set 𝒪))).toAddMonoidHom)

end Reduction
end ResidualInjectivity
end IharaTower
end P2MW.S_IharaTower_exists_eq_smul_of_iComb_eq_smul_of_isEis_kernel_pair_of_diamond_invariant
