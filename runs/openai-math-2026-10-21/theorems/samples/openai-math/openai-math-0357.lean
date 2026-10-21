namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg42093 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [13,11,6,5,5,5,4,4,3,2,2,1,1] := by
  exact rowSquare_join (by decide) sg20851 sg16103

end UniversalTensorSquare
end
end
end OAI
