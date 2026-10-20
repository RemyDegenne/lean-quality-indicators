@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace LinearMap

theorem traceOfFiniteProjective_tensorProduct'
    (R : Type uR) [CommSemiring R]
    (M : Type uM) [AddCommMonoid M] [Module R M]
    (N : Type uN) [AddCommMonoid N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    traceOfFiniteProjective R (M ⊗[R] N) (TensorProduct.map f g) =
      traceOfFiniteProjective R M f * traceOfFiniteProjective R N g := by
  have h := congr_fun₂ (traceOfFiniteProjective_tensorProduct R M N) f g
  simpa only [compr₂_apply, TensorProduct.mapBilinear_apply, compl₁₂_apply,
    lsmul_apply, smul_eq_mul] using h

end LinearMap
end
