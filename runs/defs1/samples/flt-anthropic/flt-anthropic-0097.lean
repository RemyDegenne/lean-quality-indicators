namespace P2MW.S_TateCurve_symAdd_sum_regional

open scoped NNReal

p2m_open

universe u_1 u_2

namespace TateCurve

p2m_open

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal

open IsUltrametricDist Filter Finset

namespace TateCurve

p2m_open

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {q u v : K}

set_option autoImplicit false

set_option linter.unusedSectionVars false

open scoped NNReal

open IsUltrametricDist Finset

namespace TateCurve

p2m_open

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable {q u v : K}

section MonomialConversion

def s1PosSupport (M : ℕ) : Finset ℤ := (Finset.Icc 1 M).image ((↑·) : ℕ → ℤ)

end MonomialConversion
end TateCurve
end TateCurve
end TateCurve
end P2MW.S_TateCurve_symAdd_sum_regional
