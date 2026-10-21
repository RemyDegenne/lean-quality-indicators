namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg32147 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [10,10,9,8,8,8,2,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg14312 sg21345

end UniversalTensorSquare
end
end
end OAI
