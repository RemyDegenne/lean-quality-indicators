namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg1195 : RowSquare [4,2,2,1,1,1] [2,2,2,1,1,1,1,1] := by
  exact rowSquare_join (by decide) sg4 sg330

end UniversalTensorSquare
end
end
end OAI
