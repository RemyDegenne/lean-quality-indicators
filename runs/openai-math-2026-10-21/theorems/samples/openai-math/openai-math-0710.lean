namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg11932 : RowSquare [8,6,2,2,2,2,1,1] [6,4,4,1,1,1,1,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg16 sg7259

end UniversalTensorSquare
end
end
end OAI
