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
theorem idealX_span : (idealX K).asIdeal = Ideal.span {X} := rfl

end HeightOneSpectrum
end Polynomial
end AdicValuation
end
end
