namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg5617 : RowSquare [6,4,1,1,1,1,1,1,1,1] [4,2,2,2,2,1,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg182 sg1327

end UniversalTensorSquare
end
end
end OAI
