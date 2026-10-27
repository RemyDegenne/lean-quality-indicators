public section

namespace CFSG.StandardType.GGResQTwoCellDataA4

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hcell_A4b0c1w21_2_2 :
    ggResQTwoCellCheck (CartanMatrix.A 4) 0 1 (-2) (-1) (2 : ZMod 3) (2 : ZMod 3) (w_A4b0c1w21_2_2) = true := by
  rw [show w_A4b0c1w21_2_2 = .commonKernel [2, 0, 0, 0, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [2, 0, 0, 0, 1]) (by decide +kernel)

end CFSG.StandardType.GGResQTwoCellDataA4
end
