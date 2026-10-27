namespace P2MW.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

p2m_open

universe u v

noncomputable section

namespace TwoChartCech

p2m_open

namespace GluedLinesChi

open Module Submodule

variable {k : Type u} [Field k] {s : ℕ} (a b lam : Fin s → kˣ)

abbrev Amb (k : Type u) [Field k] : Type u := k[T;T⁻¹] × k[T;T⁻¹]

end GluedLinesChi
end TwoChartCech
end
end P2MW.S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections
