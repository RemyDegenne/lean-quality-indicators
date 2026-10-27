namespace P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries

set_option autoImplicit false

namespace HeckeEis

p2m_open

namespace R2CompTT

open CongruenceSubgroup Matrix

open scoped MatrixGroups

section Main

variable {N ℓ ℓ' m : ℕ} [NeZero ℓ] [NeZero ℓ'] [NeZero m]

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

variable (ρ : Representation K (Gamma0 N) V) (a a' : V →ₗ[K] V)

variable (σ : Gamma0 N ⧸ heckeUpper N ℓ' → ↥(heckeUpper N ℓ))

variable (hσ : ∀ q', ((heckeConj N ℓ (σ q') : Gamma0 N) : Gamma0 N ⧸ heckeUpper N ℓ') = q')

variable (hm : m = ℓ * ℓ')

noncomputable def SS (Q : Gamma0 N ⧸ heckeUpper N m) : Gamma0 N :=
  ((Psi σ hσ hm).symm Q).1.out * (((σ ((Psi σ hσ hm).symm Q).2) : ↥(heckeUpper N ℓ)) : Gamma0 N)

end Main
end R2CompTT
end HeckeEis
end P2MW.S_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
