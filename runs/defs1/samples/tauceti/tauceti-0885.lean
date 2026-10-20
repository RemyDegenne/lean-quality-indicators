public section

open scoped TensorProduct

namespace TauCeti.InternalGrading

universe u v w

variable {R : Type u} {M : Type v} {N : Type w}

section Signed

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The graded tensor-dual map, with the Koszul sign in evaluation.
It is the ordinary tensor-dual map precomposed on its argument with the sign automorphism. -/
noncomputable def signedDualDistrib (G : InternalGrading R M) (H : InternalGrading R N) :
    Module.Dual R M ⊗[R] Module.Dual R N →ₗ[R] Module.Dual R (M ⊗[R] N) :=
  (G.koszulTensorTwist H).toLinearMap.dualMap ∘ₗ TensorProduct.dualDistrib R M N

end Signed
end TauCeti.InternalGrading
end
