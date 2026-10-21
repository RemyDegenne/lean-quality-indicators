namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg27416 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,9,6,5,3,2,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8414 sg10410

end UniversalTensorSquare
end
end
end OAI
