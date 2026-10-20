set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue.LevelSite

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔛 : DRModelPackageLevel N₀ q hqN)
  (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
  (κ : Type) [Field κ] [CharP κ q] [IsAlgClosed κ] [DecidableEq κ] (τ : DRLevel.R q →+* κ)

abbrev Node : Type := ↥(pullback (𝔛.comp κ τ 0) (𝔛.comp κ τ 1))

end V3Glue.LevelSite
end
