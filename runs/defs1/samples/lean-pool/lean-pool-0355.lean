@[expose] public section

namespace AtanasovRanganathan.GenusFiveTwoPoleData

open Utilities.Certificate

open Utilities.Certificate.TwoPoleSubdivision

open GenusFiveCoreAtlas

/-- Row 07, with either of its two connector slots chosen first. -/
def row07 (focus : Fin 2) : Data row07Core 4 5 4 5 :=
  if focus = 0 then row07Focus0 else row07Focus1

end AtanasovRanganathan.GenusFiveTwoPoleData
end
