namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg23881 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,6,6,5,5,3,3,2,2,2,1] := by
  exact rowSquare_join (by decide) sg8415 sg10279

end UniversalTensorSquare
end
end
end OAI
