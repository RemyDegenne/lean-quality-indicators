@[expose] public section

open Metric Set Topology unitInterval

open scoped Graph

namespace Schoenflies

open Graph

namespace HexData

variable (H : HexData)

theorem pos_mem_outerArcs (i : Fin 6) : H.pos i ∈ H.outerArcs :=
  Set.mem_iUnion.2 ⟨i, H.pos_mem_outer i⟩

end HexData
end Schoenflies
end
