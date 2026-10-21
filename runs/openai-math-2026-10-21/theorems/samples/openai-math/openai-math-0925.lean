namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg26122 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [9,7,7,6,4,3,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8796 sg9225

end UniversalTensorSquare
end
end
end OAI
