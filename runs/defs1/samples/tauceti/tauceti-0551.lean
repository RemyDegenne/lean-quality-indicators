public noncomputable section

open Filter Function MulAction Set Topology UpperHalfPlane

open TauCeti.ModularForm TauCeti.RiemannSurface TauCeti.Subgroup.CuspDatum

open _root_.Subgroup.CompactifiedQuotient

open scoped Manifold MatrixGroups

namespace TauCeti.ModularGroup

/-- The modular invariant on the compactified effective level-one quotient. At its unique pole
the assigned value is zero; its meromorphic germ there is independent of this value. -/
def jCompactified : psl2zToPSL2R.range.CompactifiedQuotient → ℂ
  | .ofQuotient p => jQuotient p
  | .ofCusp _ => 0

end TauCeti.ModularGroup
end
