public section

noncomputable section

open scoped unitInterval

open Topology

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

namespace TauCeti.UniversalCover

namespace SubgroupQuotient

/-- The distinguished point in the subgroup quotient, represented by the constant path at the
basepoint. -/
def basepoint (H : Subgroup (FundamentalGroup X x₀)) : SubgroupQuotient x₀ H :=
  Quotient.mk'' (mk x₀ (Path.Homotopic.Quotient.refl x₀))

end SubgroupQuotient
end TauCeti.UniversalCover
end
end
