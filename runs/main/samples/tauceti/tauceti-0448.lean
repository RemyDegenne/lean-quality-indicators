public section

namespace TauCeti

universe u₁ u₂ u₃

variable {R : Type*} [CommRing R]

variable {L : Type u₁} {M : Type u₂} {P : Type u₃}

variable [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]

variable [AddCommGroup P] [Module R P]

variable {σ : R →+* R}

section Quotients

variable (b : L →ₛₗ[σ] M →ₗ[R] P)

@[simp]
theorem ker_leftNumericalQuotientMk : (leftNumericalQuotientMk b).ker = leftRadical b :=
  (leftRadical b).ker_mkQ

end Quotients
end TauCeti
end
