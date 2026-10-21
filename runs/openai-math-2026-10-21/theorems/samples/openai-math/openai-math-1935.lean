namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg18718 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,6,3,3,3,2,2,2] := by
  exact rowSquare_join (by decide) sg457 sg8934

end UniversalTensorSquare
end
end
end OAI
