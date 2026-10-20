namespace P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq

set_option autoImplicit false

namespace CerednikDrinfeld

namespace FormalOmega

namespace AffineDescentAux

p2m_open

open TensorProduct

section Levels

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

abbrev Lev (F : S ≃ₐ[R] S) (k : ℕ) : Subalgebra R S :=
  AlgHom.equalizer ((F ^ k : S ≃ₐ[R] S) : S →ₐ[R] S) (AlgHom.id R S)

end Levels
end AffineDescentAux
end FormalOmega
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_FormalOmega_existsUnique_tmul_one_eq_of_map_frobenius_eq
