namespace P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree

set_option autoImplicit false

set_option linter.unusedSimpArgs false

open Polynomial PowerSeries

p2m_open

namespace ModularCurve

p2m_open

namespace PhiThreeCalc

scoped instance instCyc3 : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ

theorem ζu_val : (ζu : K3) = ζ := rfl

end PhiThreeCalc
end ModularCurve
end P2MW.S_ModularCurve_ModularPolynomialData_phi_eq_phiThree
