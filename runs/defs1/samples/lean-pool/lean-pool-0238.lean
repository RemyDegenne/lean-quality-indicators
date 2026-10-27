@[expose] public section

open Finset

namespace Hypergraph

variable {V : Type*} [DecidableEq V]

/-- The matching accumulated over `k` rounds of a strategy sequence. -/
def nibbleMatchingSeq (R : ℕ → Finset (Finset V) → Finset (Finset V)) (H : Finset (Finset V))
    (k : ℕ) : Finset (Finset V) := (nibbleIterSeq R H k).1

end Hypergraph
end
