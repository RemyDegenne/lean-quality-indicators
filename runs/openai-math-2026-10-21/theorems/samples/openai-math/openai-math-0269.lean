namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg31929 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [19,4,2,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg3755 sg14546

end UniversalTensorSquare
end
end
end OAI
