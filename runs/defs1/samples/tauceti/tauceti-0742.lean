public section

open Pointwise Set

namespace TauCeti

open RootPairing

variable {ι R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N)

variable [LinearOrder R] (b : P.Base)

/-- The set of **open Weyl chambers** of a base: the Weyl translates of the open dominant
chamber. -/
noncomputable def openWeylChambers : Set (Set M) := Set.range (openWeylChamber P b)

end TauCeti
end
