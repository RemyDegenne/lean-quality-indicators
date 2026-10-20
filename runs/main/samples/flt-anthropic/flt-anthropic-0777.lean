namespace P2MW.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open Complex UpperHalfPlane ModularForm Function Filter

open scoped Real Manifold MatrixGroups ModularForm Topology

namespace FrickeSpan

local notation "Δ" => ModularForm.discriminant

section Analytic

theorem mdifferentiable_disc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Δ : ℍ → ℂ) := CuspForm.discriminant.holo'

end Analytic
end FrickeSpan
end
end P2MW.S_CuspForm_span_frickeRational_E4_pow_E6_pow_eq_top
