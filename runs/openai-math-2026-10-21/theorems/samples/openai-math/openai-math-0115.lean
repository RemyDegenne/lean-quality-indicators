namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg18560 : RowSquare [7,6,3,3,3,2,1,1,1,1,1,1,1] [9,8,3,3,2,2,2,1,1] := by
  exact rowSquare_join (by decide) sg241 sg11172

end UniversalTensorSquare
end
end
end OAI
