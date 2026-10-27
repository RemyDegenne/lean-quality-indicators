public section

namespace TauCeti.HopfIdeal

open WithConv TrivSqZeroExt

variable {R H B : Type*} [CommRing R] [CommRing H] [HopfAlgebra R H]
  [CommRing B] [Algebra R B] {I : HopfIdeal R H}

/-- The Lie ideal of the normal closed subgroup defined by `I`, inside the ambient tangent
Lie algebra with coefficients in `B`. -/
noncomputable def IsNormal.lieIdeal (hI : I.IsNormal) :
    LieIdeal B (Derivation R H (Bialgebra.CounitAlgebra R H B)) where
  __ := (I.lieSubalgebra (B := B)).toSubmodule
  lie_mem := hI.lie_mem_lieSubalgebra _

end TauCeti.HopfIdeal
end
