@[expose] public section

noncomputable section

open Polynomial

open Finset

universe u v w

variable {R : Type u} {S : Type*}

namespace Ideal

open Polynomial

section Semiring

variable [Semiring R]

variable {I : Ideal R[X]}

variable (I)

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
def leadingCoeff : Ideal R :=
  ⨆ n : ℕ, I.leadingCoeffNth n

end Semiring
end Ideal
end
end
