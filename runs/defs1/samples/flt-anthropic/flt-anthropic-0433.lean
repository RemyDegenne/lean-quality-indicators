namespace P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv

set_option autoImplicit false

noncomputable section

p2m_open

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace B2a

p2m_open

variable {F : Type*} [Field F]

variable {W₁ W₂ : WeierstrassCurve F}
  (e : W₂.toAffine.FunctionField ≃ₐ[F] W₁.toAffine.FunctionField)

abbrev vPull : Valuation W₂.toAffine.FunctionField (WithZero (Multiplicative ℤ)) :=
  (valuationInfty W₁.toAffine).comap (e : W₂.toAffine.FunctionField →+* W₁.toAffine.FunctionField)

end B2a
end WeierstrassCurve
end
end P2MW.S_WeierstrassCurve_exists_variableChange_smul_eq_of_functionField_algEquiv
