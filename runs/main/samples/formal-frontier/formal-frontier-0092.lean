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

theorem weightOneInitial_ne_zero {p : P} (hp : p ≠ 0) :
    weightOneInitial S i p ≠ 0 := by
  have hne : weightOneExpansion S i p ≠ 0 := by
    intro h
    have hdegree := weightOneExpansion_trailingDegree S i p
    rw [h, Polynomial.trailingDegree_zero] at hdegree
    exact hp ((weightOneOrder_eq_top S p).mp hdegree.symm)
  have hdegree : (weightOneExpansion S i p).natTrailingDegree = weightOneNatOrder S p := by
    simpa [Polynomial.natTrailingDegree, weightOneNatOrder] using
      congrArg ENat.toNat (weightOneExpansion_trailingDegree S i p)
  simpa [weightOneInitial, ← hdegree, Polynomial.trailingCoeff] using
    (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hne)

end Field
end MvPolynomial
end
