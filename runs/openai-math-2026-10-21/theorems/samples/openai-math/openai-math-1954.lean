namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg31089 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [10,9,6,6,2,2,2,2,1,1,1,1] := by
  exact rowSquare_join (by decide) sg8647 sg9989

end UniversalTensorSquare
end
end
end OAI
