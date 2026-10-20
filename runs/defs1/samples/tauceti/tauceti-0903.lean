public section

open Algebra.TensorProduct WithConv

open scoped TensorProduct

namespace TauCeti

namespace AlgHom

universe u v w x

variable {R : Type u} {H : Type v} (A : Type w) (B : Type x)

variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]

section CommRing

variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]

variable [IsScalarTower R A B] [Module.FaithfullyFlat A B]

/-- **Faithfully flat descent for affine group-valued points.** If `B` is faithfully flat over
`A`, base change identifies the convolution group of `A`-points of `H` with the subgroup of
`B`-points whose two restrictions to `B ⊗[A] B` agree. -/
noncomputable def faithfullyFlatDescentMulEquiv :
    WithConv (H →ₐ[R] A) ≃* descentSubgroup (R := R) (H := H) A B :=
  MulEquiv.ofBijective (faithfullyFlatDescentHom (R := R) (H := H) A B)
    (faithfullyFlatDescentHom_bijective (R := R) (H := H) A B)

end CommRing
end AlgHom
end TauCeti
end
