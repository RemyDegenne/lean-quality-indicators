@[expose] public section

universe uR uM uN

open scoped TensorProduct

namespace LinearMap

variable (R : Type uR) [CommSemiring R]

variable (M : Type uM) [AddCommMonoid M] [Module R M]

variable (N : Type uN) [AddCommMonoid N] [Module R N]

theorem traceOfFiniteProjective_coprod_prod
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : N →ₗ[R] M) (k : M →ₗ[R] N) :
    traceOfFiniteProjective R (M × N) ((f.prod k).coprod (h.prod g)) =
      traceOfFiniteProjective R M f + traceOfFiniteProjective R N g := by
  have hBlocks : (f.prod k).coprod (h.prod g) =
      ((LinearMap.inl R M N).comp (f.comp (LinearMap.fst R M N)) +
        (LinearMap.inl R M N).comp (h.comp (LinearMap.snd R M N))) +
      ((LinearMap.inr R M N).comp (k.comp (LinearMap.fst R M N)) +
        (LinearMap.inr R M N).comp (g.comp (LinearMap.snd R M N))) := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;>
      simp [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply]
  rw [hBlocks, map_add, map_add, map_add,
    LinearMap.traceOfFiniteProjective_inl_fst,
    LinearMap.traceOfFiniteProjective_inl_snd,
    LinearMap.traceOfFiniteProjective_inr_fst,
    LinearMap.traceOfFiniteProjective_inr_snd, add_zero, zero_add]

end LinearMap
end
