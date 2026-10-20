namespace P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial

set_option autoImplicit false

universe u

open Polynomial

open scoped TensorProduct

namespace U4b

section Identification

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  [Algebra R[X] A] [IsScalarTower R R[X] A]
  (S : Type u) [CommRing S] [Algebra R S] [Algebra R[X] S] [IsScalarTower R R[X] S]
  (f : A) (s : S) (hf : algebraMap R[X] A X = f) (hs : algebraMap R[X] S X = s)

noncomputable def fwd : S ⊗[R] A →ₐ[S] S ⊗[R[X]] A :=
  AlgHom.liftEquiv R S A (S ⊗[R[X]] A)
    ((Algebra.TensorProduct.includeRight (R := R[X]) (A := S) (B := A)).restrictScalars R)

end Identification
end U4b
end P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial
