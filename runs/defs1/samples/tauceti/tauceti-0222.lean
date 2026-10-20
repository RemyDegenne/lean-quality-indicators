public noncomputable section

open Filter Function MulAction OnePoint Set Topology UpperHalfPlane

open TauCeti.ModularForm TauCeti.RiemannSurface TauCeti.Subgroup.CuspDatum

open _root_.Subgroup.CompactifiedQuotient

open scoped ContDiff Manifold MatrixGroups

namespace TauCeti.ModularGroup

/-- The normalized modular invariant identifies the compactified level-one modular quotient
biholomorphically with the Riemann sphere. -/
def jBiholomorph : psl2zToPSL2R.range.CompactifiedQuotient ≃ₘ⟮𝓘(ℂ), 𝓘(ℂ)⟯ OnePoint ℂ :=
  biholomorphOfDegreeEqOne jFiniteHolomorphicMap (by simp)

end TauCeti.ModularGroup
end
