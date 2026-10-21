namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg30418 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,8,6,5,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg8425 sg10372

end UniversalTensorSquare
end
end
end OAI
