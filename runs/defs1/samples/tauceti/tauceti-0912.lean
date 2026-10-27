public section

open CategoryTheory

open TauCeti.CommHopfAlgCat
  (geometricallyConnectedCommHopfAlgProperty_commonKernelQuotient_of_geometricallyConnected)

namespace TauCeti.D4Tripled.Generated.Positive

universe u

noncomputable section

variable (A : Type u) [CommRing A]

/-- The defining ideal of the smallest closed subgroup of the generated tripled carrier
containing its four positive numbered roots and its weight torus. -/
abbrev definingIdeal : HopfIdeal A (generatedCoordinateHopfAlgebra A) :=
  CommHopfAlgCat.commonKernelHopfIdeal (generator A)

end
end TauCeti.D4Tripled.Generated.Positive
end
