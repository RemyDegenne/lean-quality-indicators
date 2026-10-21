namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg28033 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,5,4,3,3,3,3,3,3,3,2,1] := by
  exact rowSquare_join (by decide) sg8680 sg9657

end UniversalTensorSquare
end
end
end OAI
