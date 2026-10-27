@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

namespace DSStructAux

variable {V : Type*} {G : SimpleGraph V}

namespace CentreData

variable {Γ : PairGraph} (C : CentreData Γ)

/-- The edge that carries a vertex: its unique source when it is a leaf, the centre source of
its component when it is a centre. -/
def edgeAt (v : Γ.V) : Γ.Edge :=
  ⟨s(v, C.mate v), by simpa using C.mate_adj v⟩

end CentreData
end DSStructAux
end TriangleInflation.Graph
end
