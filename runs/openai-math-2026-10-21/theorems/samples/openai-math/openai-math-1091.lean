namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg11347 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,5,5,4,3,1] := by
  exact rowSquare_join (by decide) sg1332 sg1767

end UniversalTensorSquare
end
end
end OAI
