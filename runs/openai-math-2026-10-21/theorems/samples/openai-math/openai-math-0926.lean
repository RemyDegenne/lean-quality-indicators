namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Balance Saxl.Columns

lemma degreeTreeAll37 : degreeTree37.All
    (fun rs => SquareOccurs (candidate 6 4 0) (rowDiagram rs)) := by
  have hp : rowDiagram [10,9,4,3,2,2,2,2,2,1] = candidate 6 4 0 := rowDiagram_candidate (M := 6) (b := 4) (δ := 0) (by decide)
  rw [← hp]
  exact degreeTree37_0All

end UniversalTensorSquare
end
end
end OAI
