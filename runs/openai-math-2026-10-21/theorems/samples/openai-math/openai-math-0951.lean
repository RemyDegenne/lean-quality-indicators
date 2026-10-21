namespace OAI

noncomputable section

universe u v w z

namespace Thomason.NormalizedChains

open DirectedComplex

variable {E : Type u} [PartialOrder E]

lemma edgeTable_target (a b : E) (hab : a ≤ b) :
    Table.truncate 0 true (edgeTable a b hab) = vertexTable b := by
  ext p e
  cases p with
  | zero => rfl
  | succ p => simp [Table.truncate_row, vertexTable_row_pos b (by omega : 0 < p+1)]

end Thomason.NormalizedChains
end
end OAI
