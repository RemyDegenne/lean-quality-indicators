@[expose] public section

open scoped WithZero

universe u v

namespace MvPolynomial

variable {σ : Type v}

section Field

variable {k : Type u} [Field k] (S : Set σ) (i : S)

local notation "P" => MvPolynomial σ k

local notation "K" => FractionRing P

local notation "Cw" => WeightOneCoefficientField k S i

local notation "Aw" => MvPolynomial (WeightOneCoefficientVariables S i) k

/-- Substitute the pivot by `X`, other weighted variables by `X` times their
ratio, and unweighted variables by coefficient-field generators. -/
noncomputable def weightOneExpansion : P →+* Polynomial Cw := by
  classical
  exact (aeval fun j : σ =>
    if h : j = (i : σ) then Polynomial.X
    else if hS : j ∈ S then
      Polynomial.X * Polynomial.C (algebraMap Aw Cw (X (Sum.inr ⟨j, hS, h⟩)))
    else Polynomial.C (algebraMap Aw Cw (X (Sum.inl ⟨j, hS⟩)))).toRingHom

end Field
end MvPolynomial
end
