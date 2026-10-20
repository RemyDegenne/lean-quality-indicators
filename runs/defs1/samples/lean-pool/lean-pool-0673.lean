@[expose] public section

namespace Sabidussi

namespace LoopMultigraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

variable {V E : Type*} [Fintype V] [Fintype E]

namespace EulerTour

variable [DecidableEq V] {G : LoopMultigraph V E} (T : G.EulerTour)

/-- The next edge position. -/
def next (i : T.Pos) : T.Pos := finRotate (T.n + 1) i

end EulerTour
end LoopMultigraph
end Sabidussi
end
