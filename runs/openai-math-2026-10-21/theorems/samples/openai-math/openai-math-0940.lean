namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg11299 : RowSquare [6,6,2,1,1,1,1,1,1,1,1,1] [5,4,3,3,2,2,2,2] := by
  exact rowSquare_join (by decide) sg1334 sg1757

end UniversalTensorSquare
end
end
end OAI
