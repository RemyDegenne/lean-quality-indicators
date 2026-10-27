set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Asm

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

variable (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)}) (H : SiteHyps p 𝔛 O κ toκ)

def R : V3Glue.RawChartInput (V3Glue.Site.XO p O) (V3Glue.Site.Node p 𝔛 κ) :=
  V3Glue.Site.rawChartInputOfDR p 𝔛 O κ (bc p O κ toκ) hϖ H.model H.hC H.hxinj H.hxcl

end V3Asm
end
