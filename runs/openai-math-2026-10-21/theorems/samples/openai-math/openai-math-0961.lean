namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg8965 : RowSquare [5,4,1,1,1,1,1,1,1,1,1,1,1,1,1] [9,3,3,3,1,1,1,1] := by
  exact rowSquare_join (by decide) sg1503 sg1555

end UniversalTensorSquare
end
end
end OAI
