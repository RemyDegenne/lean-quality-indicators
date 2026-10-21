namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open scoped Classical

lemma card_tupleCrossEdges_le (S : Finset (Fin tupleBlocks))
    (b : Fin tupleBlocks) (hb : b ∉ S) {α β : Fin tupleH} (hne : α ≠ β) :
    (cutCrossEdges (tupleUnmarkedGraph S b hb hne)).card ≤ (Fintype.card TupleVertex)^2 :=
  card_relation_le_sq _ (card_tupleHalfEntry_le S b hb α β)

end SquareDifference
end
end OAI
