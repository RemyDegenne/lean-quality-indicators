namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg19538 : RowSquare [7,7,3,2,2,1,1,1,1,1,1,1,1,1,1] [10,4,4,3,3,3,2,2] := by
  exact rowSquare_join (by decide) sg165 sg11694

end UniversalTensorSquare
end
end
end OAI
