namespace P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane hiding I

open MeasureTheory Filter Complex Set Metric

open scoped MatrixGroups Topology Real ComplexConjugate ModularForm

namespace ModularCurve

namespace DivisorFunction

p2m_open

local notation "𝕌" => UpperHalfPlane.upperHalfPlaneSet

local notation "Γ₀" => CongruenceSubgroup.Gamma0

theorem ofComplex_coe (τ : ℍ) : ofComplex (τ : ℂ) = τ := ofComplex_apply τ

end DivisorFunction
end ModularCurve
end
end P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate
