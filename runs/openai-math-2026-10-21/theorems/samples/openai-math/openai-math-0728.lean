namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg6177 : RowSquare [5,5,1,1,1,1,1,1,1,1,1] [3,3,2,2,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg586 sg998

end UniversalTensorSquare
end
end
end OAI
