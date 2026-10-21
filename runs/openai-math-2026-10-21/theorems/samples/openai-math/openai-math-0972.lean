namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg25766 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,6,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8860 sg9091

end UniversalTensorSquare
end
end
end OAI
