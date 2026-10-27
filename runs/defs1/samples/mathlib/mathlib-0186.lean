variable {K : Type*} [Field K]

open IntermediateField

namespace RatFunc.Luroth

noncomputable section

open algebraAdjoinAdjoin Polynomial

open scoped Polynomial.Bivariate

variable {E : IntermediateField K K⟮X⟯}

variable (E) in
/-- A polynomial `q` that satisfies `φ * q = (generator E).minpolyX`. -/
abbrev q : E[X] := φ_dvd_generator_minpolyX.choose

end
end RatFunc.Luroth
