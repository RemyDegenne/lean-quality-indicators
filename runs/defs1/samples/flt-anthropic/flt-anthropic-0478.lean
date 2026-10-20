namespace P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div

set_option autoImplicit false

noncomputable section

open Filter Topology Polynomial

open scoped PowerSeries.WithPiTopology

namespace ModularCurve

namespace SiegelUnit

namespace L2

p2m_open

namespace EulerProdFam

section Formal

variable {R : Type*} [CommRing R]

variable {P : ℕ → R[X]}

section Topological

variable [TopologicalSpace R]

def W (P : ℕ → R[X]) : PowerSeries R := ∏' n : ℕ, fac P n

end Topological
end Formal
end EulerProdFam
end L2
end SiegelUnit
end ModularCurve
end
end P2MW.S_ModularCurve_SiegelUnit_hasSum_coeff_siegelSeries_pow_mul_exp_siegelFun_pow_div
