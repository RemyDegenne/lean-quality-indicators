@[expose] public section

open Polynomial

namespace FrobeniusTwistedLine

open scoped TensorProduct

noncomputable section

variable (K : Type*) [Field K]

variable {K}

theorem SatisfiesEquation.add {A : Type*} [CommRing A] [Algebra K A]
    {p : ℕ} [Fact p.Prime] [CharP A p] {t : K} {x₁ y₁ x₂ y₂ : A}
    (h₁ : SatisfiesEquation p t x₁ y₁) (h₂ : SatisfiesEquation p t x₂ y₂) :
    SatisfiesEquation p t (x₁ + x₂) (y₁ + y₂) := by
  rw [SatisfiesEquation, add_pow_char, add_pow_char, sub_eq_zero]
  rw [SatisfiesEquation, sub_eq_zero] at h₁ h₂
  exact (congrArg₂ (· + ·) h₁ h₂).trans (mul_add _ _ _).symm

end
end FrobeniusTwistedLine
end
