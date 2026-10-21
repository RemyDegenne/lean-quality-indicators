namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Balance Saxl.Columns

lemma degreeCheck42_2_3 :
    ∀ a ∈ List.range degreeRows42_0.length, ∀ c ∈ List.range degreeRows42_0.length,
      residualCheck 42 8 3 3 4 (a+1) (c+1) degreeRows42_0 degreeP42 := by
  decide +kernel

end UniversalTensorSquare
end
end
end OAI
