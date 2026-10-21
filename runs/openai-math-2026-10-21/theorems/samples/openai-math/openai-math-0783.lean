namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Balance Saxl.Columns

lemma degreeCones61 : ∀ q ∈ degreeQs61, ∀ μ : YoungDiagram, μ.card = 61 →
    RowsDom μ.rowLens q → SquareOccurs (candidate 10 1 1) μ := by
  intro q hq
  simp only [degreeQs61,List.not_mem_nil] at hq

end UniversalTensorSquare
end
end
end OAI
