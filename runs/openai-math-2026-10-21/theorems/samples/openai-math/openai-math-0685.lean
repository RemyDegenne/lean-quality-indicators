namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg24701 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,8,6,6,5,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg5265 sg12681

end UniversalTensorSquare
end
end
end OAI
