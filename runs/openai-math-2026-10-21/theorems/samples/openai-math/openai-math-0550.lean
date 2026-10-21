namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg42490 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,9,8,6,3,3,3,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19524

end UniversalTensorSquare
end
end
end OAI
