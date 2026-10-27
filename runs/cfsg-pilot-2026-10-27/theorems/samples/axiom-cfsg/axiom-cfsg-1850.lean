public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum

theorem N0_le_gammaU : N0 ≤ gammaU := N0_le_M0.trans M0_le_gammaU

end CFSG.GF2Type.Smith1979.IdxFour
end
