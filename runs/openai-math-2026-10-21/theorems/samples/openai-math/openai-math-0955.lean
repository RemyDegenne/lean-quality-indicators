namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Columns Saxl.Balance

lemma sg15725 : RowSquare [5,4,4,4,3,2,1,1,1,1,1,1,1,1,1] [7,5,5,5,2,2,2,2,1] := by
  exact rowSquare_join (by decide) sg3692 sg4124

end UniversalTensorSquare
end
end
end OAI
