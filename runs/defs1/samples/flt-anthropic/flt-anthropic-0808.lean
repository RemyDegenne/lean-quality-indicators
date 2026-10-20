namespace P2MW.S_TateCurve_diffHyp_unconditional

set_option linter.unusedSectionVars false

open scoped NNReal

p2m_open

universe u_1 u_2

namespace TateCurve

p2m_open

set_option autoImplicit false

set_option linter.unusedSectionVars false

p2m_reactivate

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace TateCurve

p2m_open

open IsUltrametricDist

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {u v : K}

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section CrossInteriorTable

noncomputable def fgCoeff (t : ℕ) : K := if t = 0 then 1 else if t = 1 then -1 else -2

end CrossInteriorTable
end TateCurve
end TateCurve
end P2MW.S_TateCurve_diffHyp_unconditional
