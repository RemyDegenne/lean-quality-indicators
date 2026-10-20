@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]

variable (M : Type uM) [AddCommMonoid M] [Module R M]

variable (N : Type uN) [AddCommMonoid N] [Module R N]

section FiniteProjectiveFactors

variable [Module.Finite R M] [Module.Projective R M]

variable [Module.Finite R N] [Module.Projective R N]

theorem traceOfFiniteProjective_inl_fst (f : M →ₗ[R] M) :
    traceOfFiniteProjective R (M × N)
        ((inl R M N).comp (f.comp (fst R M N))) =
      traceOfFiniteProjective R M f := by
  have h : (inl R M N).comp (f.comp (fst R M N)) =
      prodMap f (0 : N →ₗ[R] N) := by
    apply LinearMap.ext
    intro x
    simp only [comp_apply, inl_apply, fst_apply, prodMap_apply, zero_apply]
  rw [h, traceOfFiniteProjective_prodMap_zero]

end FiniteProjectiveFactors
end LinearMap
end
