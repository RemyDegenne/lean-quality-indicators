namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck60_1_2 :
    ∀ a ∈ List.range degreeRows60_0.length, ∀ c ∈ List.range degreeRows60_0.length,
      residualCheck 60 8 12 2 3 (a+1) (c+1) degreeRows60_0 degreeP60 := by
  decide +kernel

end UniversalTensorSquare
end
end
end OAI
