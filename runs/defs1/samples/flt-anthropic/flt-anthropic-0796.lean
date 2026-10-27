namespace P2MW.S_ModularCurve_hasSum_coeff_etaProd_pow

set_option maxHeartbeats 3200000

set_option autoImplicit false

p2m_open

noncomputable section

namespace ModularCurve

p2m_open

namespace EtaQSeries

open Filter Topology Polynomial

open scoped PowerSeries.WithPiTopology

def p (N : ℕ) : Polynomial ℤ := ∏ n ∈ Finset.range N, ((1 : Polynomial ℤ) - Polynomial.X ^ (n + 1))

end EtaQSeries
end ModularCurve
end
end P2MW.S_ModularCurve_hasSum_coeff_etaProd_pow
