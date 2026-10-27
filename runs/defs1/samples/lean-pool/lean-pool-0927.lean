@[expose] public section

open Finset

namespace Finset

variable {V : Type*} [DecidableEq V]

/-- The set of vertices incident with an edge of the finite edge set `E`. -/
def edgeSupport (E : Finset (Sym2 V)) : Finset V := E.biUnion Sym2.toFinset

end Finset
end
