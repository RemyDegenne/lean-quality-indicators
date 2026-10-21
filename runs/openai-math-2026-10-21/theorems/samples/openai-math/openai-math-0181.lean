namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg33235 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [11,10,10,9,5,4,3,2,2,2,2,2] := by
  exact rowSquare_join (by decide) sg18911 sg19725

end UniversalTensorSquare
end
end
end OAI
