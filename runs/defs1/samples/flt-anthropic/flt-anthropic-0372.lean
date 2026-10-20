namespace P2MW.S_TwoChartCech_exists_semilinearEquiv_gluedLinesSections_of_invertible

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 3200000

p2m_open

open scoped TensorProduct

universe u

noncomputable section

namespace TwoChartCech

p2m_open

namespace GluedLinesModel

variable {k : Type u} [Field k] {s : ℕ}

variable (a b : Fin s → kˣ) (ha : Function.Injective a) (hb : Function.Injective b)

def w₁' (μ : Fin s → kˣ) : k[T;T⁻¹] × k[T;T⁻¹] := (lagrInv a (fun i => (μ i : k)), 1)

end GluedLinesModel
end TwoChartCech
end
end P2MW.S_TwoChartCech_exists_semilinearEquiv_gluedLinesSections_of_invertible
