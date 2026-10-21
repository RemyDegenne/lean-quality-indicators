namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg11905 : RowSquare [8,6,2,2,2,2,1,1] [6,3,3,3,3,3,1,1,1] := by
  exact rowSquare_join (by decide) sg0 sg11523

end UniversalTensorSquare
end
end
end OAI
