@[expose] public section

open Filter Function MeasureTheory Set

open scoped ENNReal Topology

namespace QuadraticCarleson.PositiveFullMaximalMeasurability

open PositivePrincipalValueEndpoints HilbertFiniteTruncationWeakOneOne

noncomputable
section

/-- Convolution of a test function with the quadratic difference kernel. -/
def quadraticDifferenceIntegral (lam : ℝ) (f : L0Infinity) (x : ℝ) : ℂ :=
  ∫ t, f (x - t) * quadraticDifferenceKernel lam t

end
end QuadraticCarleson.PositiveFullMaximalMeasurability
end
