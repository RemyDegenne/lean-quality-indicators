namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg21459 : RowSquare [10,8,4,3,2,2,2,2,1,1] [10,4,3,3,2,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg4720 sg5618

end UniversalTensorSquare
end
end
end OAI
