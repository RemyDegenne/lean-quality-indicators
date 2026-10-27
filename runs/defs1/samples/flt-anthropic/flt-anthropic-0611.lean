namespace P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top

set_option autoImplicit false

noncomputable section

p2m_open

open scoped Manifold ContDiff Topology

namespace AlgebraicCurve

namespace SpanRealProof

p2m_open

section PathCalculus

variable {F : Type*} [Field F] [Algebra ℂ F]

variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def transPrimitive (g h : unitInterval → ℂ) : unitInterval → ℂ := fun t =>
  if (t : ℝ) ≤ 1 / 2 then Set.IccExtend zero_le_one g (2 * t)
  else Set.IccExtend zero_le_one h (2 * t - 1) + (g 1 - h 0)

end PathCalculus
end SpanRealProof
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_span_real_pathPeriodLattice_eq_top
