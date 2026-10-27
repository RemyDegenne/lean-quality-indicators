@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open Utilities.Certificate

open Utilities.Certificate.CoreOrbitReduction

open Utilities.Certificate.ContractionForestCensusGeneral

variable {n p : ℕ} {core : ExplicitPotential.Core n p}

namespace ClosedAuto

namespace AutoData

/-- Decode a proposed vertex image using zero for missing entries and reduction modulo the
nonzero vertex count. -/
def vertexMap (d : AutoData) (hn : 0 < n) (v : Fin n) : Fin n :=
  ⟨d.vertex.getD v.val 0 % n, Nat.mod_lt _ hn⟩

end AutoData
end ClosedAuto
end Utilities.Subdivision.ClosedRowProof
end
