public section

open scoped TensorProduct

namespace TauCeti

universe u v w

namespace InternalGrading

section Signs

variable {R : Type u} [CommRing R]

variable {M : Type v} {N : Type w}

variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The Koszul sign automorphism of a graded tensor product. On bidegree `(p,q)` it
multiplies by `(-1)^(p*q)`, without interchanging the factors. -/
noncomputable def koszulTensorTwist (G : InternalGrading R M) (H : InternalGrading R N) :
    M ⊗[R] N ≃ₗ[R] M ⊗[R] N :=
  TensorProduct.congr G.quadraticTwistEquiv H.quadraticTwistEquiv ≪≫ₗ
    (G.tensorProduct H).quadraticTwistEquiv

end Signs
end InternalGrading
end TauCeti
end
