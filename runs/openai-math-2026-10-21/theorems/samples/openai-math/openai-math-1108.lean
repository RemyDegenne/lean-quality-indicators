namespace OAI

section

noncomputable section

namespace UniversalTensorSquare

open Saxl Saxl.Balance Saxl.Columns

lemma degreeCover62_3_2 :
    ∀ a ∈ List.range degreeRows62_0.length, ∀ c ∈ List.range degreeRows62_0.length,
      regionCheck 62 8 13 4 3 (a+1) (c+1) degreeRows62_0 degreeRegions62 := by
  decide +kernel

end UniversalTensorSquare
end
end
end OAI
