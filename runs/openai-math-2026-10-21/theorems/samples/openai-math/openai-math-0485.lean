namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg40558 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,8,8,6,6,6,5,2,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20316 sg18696

end UniversalTensorSquare
end
end
end OAI
