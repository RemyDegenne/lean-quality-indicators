namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg38992 : RowSquare [15,13,6,5,4,3,2,2,2,2,2,2,2,1,1] [12,11,7,5,5,5,5,4,3,2,2,1] := by
  exact rowSquare_join (by decide) sg18913 sg19969

end UniversalTensorSquare
end
end
end OAI
