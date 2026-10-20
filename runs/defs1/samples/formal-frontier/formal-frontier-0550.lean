public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

namespace IsQuasiFlasque

variable (F : Sheaf AddCommGrpCat.{u} X)

/-- The cokernel of the canonical map to the flasque injective envelope. -/
abbrev flasqueInjectiveQuotient : Sheaf AddCommGrpCat.{u} X :=
  cokernel (toFlasqueInjectiveEnvelope F)

end IsQuasiFlasque
end TopCat.Sheaf
end
end
