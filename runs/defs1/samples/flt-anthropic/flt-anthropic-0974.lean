namespace P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential

set_option autoImplicit false

noncomputable section

p2m_open

open scoped Manifold ContDiff Topology

namespace AlgebraicCurve

namespace ChartPrimitiveTransportProof

p2m_open

section Derivation

variable {F : Type*} [Field F] [Algebra ℂ F]

variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

variable [IsCurveOver ℂ F] [T2Space (Place ℂ F)]

@[reducible] def germAlgebra (w : Place ℂ F) : Algebra F (Germ (pf w) ℂ) := (readHom w).toAlgebra

end Derivation
end ChartPrimitiveTransportProof
end AlgebraicCurve
end
end P2MW.S_AlgebraicCurve_isPrimitiveAlong_comp_extChartAt_of_hasDerivAt_readDifferential
