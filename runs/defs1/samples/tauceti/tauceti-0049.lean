public section

namespace TauCeti

open scoped Pointwise

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]

local notation "U" => _root_.UniversalEnvelopingAlgebra R (heisenberg R)

local notation "I" => (HopfIdeal.toIdeal (HopfIdeal.augmentation R U))

/-- The truncated enveloping algebra of the Heisenberg algebra, killing products of three
augmented elements while retaining the central bracket. -/
noncomputable abbrev heisenbergAugmentationQuotient := U ⧸ I ^ 3

end TauCeti
end
