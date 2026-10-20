@[expose] public section

noncomputable section

universe u v w x y

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)

variable {M : Type v} [AddCommGroup M] [Module R M]

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Extend a linear map to an adically complete target using the completed map.
The completed-ring-linear inner map is explicitly restricted to `R`-scalars. -/
noncomputable def extend [IsAdicComplete I N] (f : M →ₗ[R] N) :
    AdicCompletion I M →ₗ[R] N :=
  (ofLinearEquiv I N).symm.toLinearMap.comp ((map I f).restrictScalars R)

end AdicCompletion
end
end
