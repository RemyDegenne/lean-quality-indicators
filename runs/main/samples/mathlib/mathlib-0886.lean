@[expose] public section

noncomputable section

open Polynomial Set Function Finsupp AddMonoidAlgebra

universe u v w x

variable {R : Type u} {S₁ : Type v} {S₂ : Type w} {S₃ : Type x}

namespace MvPolynomial

variable {σ : Type*} {a : R} {e : ℕ} {s : σ →₀ ℕ}

section Equiv

variable (R) [CommSemiring R]

section

variable (S₁ S₂ S₃)

lemma optionEquivRight_X_none : optionEquivRight R S₁ (X none) = C Polynomial.X := by
  simp [optionEquivRight_apply, aeval_X]

end
end Equiv
end MvPolynomial
end
end
