@[expose] public section

noncomputable section

universe u

variable {K : Type u}

section AdicValuation

variable (K : Type*) [Field K]

namespace Polynomial

open RatFunc

section HeightOneSpectrum

open IsDedekindDomain.HeightOneSpectrum WithZero

@[simp]
theorem valuation_X_eq_neg_one :
    (idealX K).valuation K⟮X⟯ RatFunc.X = exp (-1 : ℤ) := by
  rw [← RatFunc.algebraMap_X, valuation_of_algebraMap, intValuation_singleton
      _ (Polynomial.X_ne_zero) (idealX_span K)]

end HeightOneSpectrum
end Polynomial
end AdicValuation
end
end
