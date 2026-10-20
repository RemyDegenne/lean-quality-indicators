@[expose] public section

universe uR uM uN uF

namespace LinearMap

universe uι

@[simp]
theorem bidualEvalEquiv_apply
    (R : Type uR) (M : Type uM)
    [Semiring R] [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (m : M) (f : M →ₗ[R] R) :
    bidualEvalEquiv R M m f = f m := rfl

end LinearMap
end
