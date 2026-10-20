public section

noncomputable section

open CategoryTheory Topology

universe u

namespace TauCeti

namespace TransitiveFundamentalGroupoidAction

variable {X : TopCat.{u}}

/-- The inclusion into fibrewise pretransitive actions is fully faithful. -/
def fullyFaithfulForget (X : TopCat.{u}) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

end TransitiveFundamentalGroupoidAction
end TauCeti
end
end
