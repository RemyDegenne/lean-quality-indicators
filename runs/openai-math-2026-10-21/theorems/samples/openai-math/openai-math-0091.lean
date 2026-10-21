namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg33063 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,9,9,9,3,3,3,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg20508 sg17278

end UniversalTensorSquare
end
end
end OAI
