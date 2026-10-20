set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section LevelLegs

variable (K : Type*) [Field K] (M s : ℕ) [NeZero M] [NeZero s]

def autOnPlaces (σ : modularFunctionFieldC K (M * s) ≃ₐ[K] modularFunctionFieldC K (M * s)) :
    Place K (modularFunctionFieldC K (M * s)) ≃ Place K (modularFunctionFieldC K (M * s)) :=
  Place.congrEquiv σ.toRingEquiv (fun c => σ.commutes c)

end LevelLegs
end ModularCurve
end
