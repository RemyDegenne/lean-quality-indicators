public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

/-- The product of the stalk-skyscraper endofunctors over all points. -/
noncomputable abbrev flasqueEnvelopeFunctor :
    Sheaf AddCommGrpCat X ⥤ Sheaf AddCommGrpCat X :=
  ∏ᶜ fun x : X => stalkSkyscraperFunctor x

end TopCat.Sheaf
end
end
