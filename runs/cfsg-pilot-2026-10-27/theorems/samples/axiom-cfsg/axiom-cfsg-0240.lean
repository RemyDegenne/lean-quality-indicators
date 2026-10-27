public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup

open CFSG.LocalAnalysis.GLTheoremA.CatB

theorem K5_card : Nat.card K5 = 60 := by
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), a8Kb_card]

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
end
