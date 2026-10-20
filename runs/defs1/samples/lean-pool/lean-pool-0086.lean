@[expose] public section

namespace AtanasovRanganathan.GenusFiveCubicAtlas

open Utilities

open Utilities.Certificate

open Utilities.Certificate.ExplicitPotential

open AtanasovRanganathan.GenusFiveCoreAtlas

/-- Atlas row 11, bundling `row11Core` with its looplessness, connectivity, and cubic-degree
proofs. -/
def row11 : Row := ⟨row11Core, row11_loopless, row11_connected, row11_trivalent⟩

end AtanasovRanganathan.GenusFiveCubicAtlas
end
