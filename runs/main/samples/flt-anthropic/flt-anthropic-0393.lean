namespace P2MW.S_HaarQuotient_lintegral_density_mul_eq_one

set_option autoImplicit false

open MeasureTheory Topology

open scoped ENNReal Pointwise

namespace HaarQuotient

p2m_open

namespace SEC

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

theorem measurable_weight_mul (g : G) : Measurable fun y : H => weight H μH ((y : G) * g) :=
  (measurable_weight H μH).comp (continuous_subtype_val.mul continuous_const).measurable

end SEC
end HaarQuotient
end P2MW.S_HaarQuotient_lintegral_density_mul_eq_one
