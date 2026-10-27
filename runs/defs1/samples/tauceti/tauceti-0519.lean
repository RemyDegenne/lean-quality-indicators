public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}

variable [AddCommGroup Vℤ]

variable [AddCommGroup Vℚ] [Module ℚ Vℚ]

variable [AddCommGroup Vℂ] [Module ℂ Vℂ]

variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

section OfPure

variable (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)

variable (Vℚ) in
/-- The weight filtration concentrated in a single degree `n`: everything from degree `n` on,
zero below. It is the weight filtration of a pure Hodge structure of weight `n`. -/
def concentratedWeightFiltration (n : ℤ) : ℤ → Submodule ℚ Vℚ :=
  fun k ↦ if n ≤ k then ⊤ else ⊥

end OfPure
end TauCeti.Hodge
end
