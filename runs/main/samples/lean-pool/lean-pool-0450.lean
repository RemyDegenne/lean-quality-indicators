@[expose] public section

namespace LeanEval

namespace Topology

namespace ClassificationOfSurfaces

namespace Moise

namespace TriangleMesh

variable (M : TriangleMesh)

theorem oppositeCoord_mem_coordinateLines (t : M.Triangle) (k : Fin 3) :
    M.oppositeCoord t k ∈ M.coordinateLines := by
  simp [coordinateLines]

end TriangleMesh
end Moise
end ClassificationOfSurfaces
end Topology
end LeanEval
end
