variable {K : Type*} [Field K]

open IntermediateField

namespace RatFunc.Luroth

noncomputable section

open algebraAdjoinAdjoin Polynomial

open scoped Polynomial.Bivariate

variable {E : IntermediateField K K⟮X⟯}

variable (E) in
/-- The minimal polynomial of `X` with coefficients in `E`. -/
abbrev φ : E[X] := minpoly E (X : K⟮X⟯)

end
end RatFunc.Luroth
