public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n : ℕ}

namespace ReidemeisterThree

/-- Include the twelve selected crossing slots in the ambient half-edge type. -/
def triangleEmbedding (D : PDCode n) (c : Fin 3 ↪ Fin n) :
    Fin 3 × Fin 4 ↪ Fin (4 * n) :=
  (c.prodMap (Function.Embedding.refl _)).trans
    ((crossingSlotEquiv n).toEmbedding.trans D.halfEdge.toEmbedding)

end ReidemeisterThree
end TauCeti.PDCode
end
