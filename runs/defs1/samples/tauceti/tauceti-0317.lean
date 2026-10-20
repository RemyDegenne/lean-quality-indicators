public section

open scoped TensorProduct

namespace TauCeti

universe u v

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace CompletedReducedTensorWords

/-- Forget the empty-word component of a completed coaugmented word. -/
noncomputable def ofCompleted : CompletedTensorWords R M →ₗ[R]
    CompletedReducedTensorWords R M :=
  LinearMap.pi fun n ↦ LinearMap.proj n.1

end CompletedReducedTensorWords
end TauCeti
end
