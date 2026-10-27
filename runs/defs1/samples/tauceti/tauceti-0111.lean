public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}

variable [AddCommGroup Vℤ]

variable [AddCommGroup Vℚ] [Module ℚ Vℚ]

variable [AddCommGroup Vℂ] [Module ℂ Vℂ]

variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

section Rational

variable (ιℚ) in
/-- The integral vectors of a rational subspace `U`: those vectors of the integral module whose
rationalization lies in `U`. -/
def integralSubmodule (U : Submodule ℚ Vℚ) : Submodule ℤ Vℤ :=
  (U.restrictScalars ℤ).comap ιℚ

end Rational
end TauCeti.Hodge
end
