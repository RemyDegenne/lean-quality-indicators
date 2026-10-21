namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg5123 : RowSquare [4,3,3,2,1,1,1,1,1,1] [4,4,4,2,2,1,1] := by
  exact rowSquare_join (by decide) sg389 sg941

end UniversalTensorSquare
end
end
end OAI
