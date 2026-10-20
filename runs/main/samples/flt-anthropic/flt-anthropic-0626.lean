namespace P2MW.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff

set_option autoImplicit false

noncomputable section

open PDivisibleGroup Coalgebra

p2m_open_scoped

namespace PDivOrthCR

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra R (PadicAlgCl p)]

variable {R}

variable (hO : OK p R)

section Alg

variable {h : ℕ} {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G') (w : ℕ)

theorem ev_tmul {L : Type} [CommRing L] [Algebra R L] (φ : O p R →ₐ[R] L) (z : G.level w →ₐ[R] L)
    (c : O p R) (x : G.level w) : ev p w φ z (c ⊗ₜ x) = φ c * z x :=
  Algebra.TensorProduct.lift_tmul _ _ _ c x

end Alg
end PDivOrthCR
end
end P2MW.S_PDivisibleGroup_CartierDuality_pair_pointMap_eq_one_of_forall_isNilpotent_of_isIntegral_iff
