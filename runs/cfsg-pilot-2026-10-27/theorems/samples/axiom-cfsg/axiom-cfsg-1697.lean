public section

namespace CFSG.StandardType.GGResQTwoCellDataA7

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hwits_A7b0c6 :
    GGResQTwoCellCheckAll (CartanMatrix.A 7) 0 6 (-1) (-1) wits_A7b0c6 := by
  intro u v
  rcases ggResQTwoZMod3_cases u with rfl | rfl | rfl
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_0_0) (by rfl)]
      exact hcell_A7b0c6_0_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_0_1) (by rfl)]
      exact hcell_A7b0c6_0_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_0_2) (by rfl)]
      exact hcell_A7b0c6_0_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_1_0) (by rfl)]
      exact hcell_A7b0c6_1_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_1_1) (by rfl)]
      exact hcell_A7b0c6_1_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_1_2) (by rfl)]
      exact hcell_A7b0c6_1_2
  · rcases ggResQTwoZMod3_cases v with rfl | rfl | rfl
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_2_0) (by rfl)]
      exact hcell_A7b0c6_2_0
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_2_1) (by rfl)]
      exact hcell_A7b0c6_2_1
    · rw [ggResQTwoCellAt_of_find (w := w_A7b0c6_2_2) (by rfl)]
      exact hcell_A7b0c6_2_2

end CFSG.StandardType.GGResQTwoCellDataA7
end
