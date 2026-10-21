namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg42933 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [14,8,8,6,5,5,5,5,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg19617 sg19560

end UniversalTensorSquare
end
end
end OAI
