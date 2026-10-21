namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg24893 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,7,5,4,3,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8651 sg9745

end UniversalTensorSquare
end
end
end OAI
