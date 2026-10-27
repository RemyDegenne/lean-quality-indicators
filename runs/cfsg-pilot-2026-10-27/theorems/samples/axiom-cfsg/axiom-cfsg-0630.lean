public section

namespace CFSG.StandardType.GGResQTwoCellDataA4

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hcell_A4b3c1_1_0 :
    ggResQTwoCellCheck (CartanMatrix.A 4) 3 1 (-1) (-1) (1 : ZMod 3) (0 : ZMod 3) (w_A4b3c1_1_0) = true := by
  rw [show w_A4b3c1_1_0 = .commonKernel [0, 0, 2, 1, 1] from rfl]
  exact ggResQTwoCellCheckK_imp (.commonKernel [0, 0, 2, 1, 1]) (by decide +kernel)

end CFSG.StandardType.GGResQTwoCellDataA4
end
