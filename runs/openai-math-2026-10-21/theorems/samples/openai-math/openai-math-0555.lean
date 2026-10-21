namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg19448 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [9,6,6,4,3,3] := by
  exact rowSquare_join (by decide) sg165 sg11645

end UniversalTensorSquare
end
end
end OAI
