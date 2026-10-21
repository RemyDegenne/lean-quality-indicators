namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg12865 : RowSquare [5,4,3,3,2,2,1,1,1,1,1,1,1] [6,4,4,4,4,4] := by
  exact rowSquare_join (by decide) sg2314 sg2167

end UniversalTensorSquare
end
end
end OAI
