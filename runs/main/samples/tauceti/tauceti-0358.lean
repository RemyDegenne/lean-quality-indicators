public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable {Q : Type u} [Quiver.{v} Q]

section Map

variable (k : Type w) [CommSemiring k] [Finite Q]

@[simp]
theorem ginzburgOriginalMap_vertexIdempotent (v : Q) :
    ginzburgOriginalMap k (vertexIdempotent k v) =
      vertexIdempotent (Q := GinzburgQuiver Q) k v := by
  rw [ginzburgOriginalMap, AlgHom.comp_apply, mapAlgHom_vertexIdempotent,
    ← doubledVertexIdempotent_def, ginzburgMap_doubledVertexIdempotent]

end Map
end TauCeti
end
