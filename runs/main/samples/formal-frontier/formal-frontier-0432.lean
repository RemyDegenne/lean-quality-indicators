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

@[simp] theorem weightOneExpansion_C (a : k) :
    weightOneExpansion S i (C a) = Polynomial.C (algebraMap k Cw a) := by
  simp [weightOneExpansion, IsScalarTower.algebraMap_eq k Cw (Polynomial Cw)]

end Field
end MvPolynomial
end
