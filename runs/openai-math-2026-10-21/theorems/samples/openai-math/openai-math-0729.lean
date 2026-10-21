namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg18695 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [10,5,5,3,3,3,1,1] := by
  exact rowSquare_join (by decide) sg842 sg8038

end UniversalTensorSquare
end
end
end OAI
