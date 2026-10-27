@[expose] public section

noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The inclusion cocone regarded as a cocone in `Cat`, with functors as morphisms. -/
def openCoverCatCocone (U : ι → Opens X) : Cocone (openCoverCatDiagram U) :=
  Grpd.forgetToCat.mapCocone (openCoverCocone U)

end FundamentalGroupoid
end
end
