@[expose] public section

universe uR uM

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]

variable (M : Type uM) [AddCommMonoid M] [Module R M]

variable [Module.Finite R M] [Module.Projective R M]

/-- The linear trace of a finite projective module endomorphism, obtained by
contracting its inverse image under the canonical dual tensor–Hom equivalence. -/
noncomputable def traceOfFiniteProjective : (M →ₗ[R] M) →ₗ[R] R :=
  (contractLeft R M).comp (dualTensorHomEquiv R M M).symm.toLinearMap

end LinearMap
end
