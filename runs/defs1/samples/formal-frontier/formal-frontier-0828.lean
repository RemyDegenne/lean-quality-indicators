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

/-- A chosen injective object containing the stalk of `F` at `x`. -/
abbrev stalkInjective (x : X) : AddCommGrpCat.{u} :=
  Injective.under (stalkObject F x)

end IsQuasiFlasque
end TopCat.Sheaf
end
end
