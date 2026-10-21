namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg23722 : RowSquare [12,10,4,3,2,2,2,2,2,2,1,1] [8,5,5,4,4,4,4,4,3,2] := by
  exact rowSquare_join (by decide) sg8648 sg9690

end UniversalTensorSquare
end
end
end OAI
