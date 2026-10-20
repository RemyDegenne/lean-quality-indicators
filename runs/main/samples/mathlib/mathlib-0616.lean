@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial

open Function Finsupp

variable {R : Type u} {σ : Type v} {a : R} {s : σ →₀ ℕ}

section PDeriv

variable [CommSemiring R]

@[simp]
theorem pderiv_monomial {i : σ} :
    pderiv i (monomial s a) = monomial (s - single i 1) (a * s i) := by
  classical
  simp only [pderiv_def, mkDerivation_monomial, Finsupp.smul_sum, smul_eq_mul, ← smul_mul_assoc,
    ← (monomial _).map_smul]
  refine (Finset.sum_eq_single i (fun j _ hne => ?_) fun hi => ?_).trans ?_
  · simp [Pi.single_eq_of_ne hne]
  · rw [Finsupp.notMem_support_iff] at hi; simp [hi]
  · simp

end PDeriv
end MvPolynomial
end
end
