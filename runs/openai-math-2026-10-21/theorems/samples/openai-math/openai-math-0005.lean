namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg17757 : RowSquare [6,6,3,3,2,2,1,1,1,1,1,1,1,1,1] [9,6,6,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1 sg14961

end UniversalTensorSquare
end
end
end OAI
