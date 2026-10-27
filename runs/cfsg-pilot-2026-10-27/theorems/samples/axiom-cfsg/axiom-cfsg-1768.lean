public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F]

theorem fixSp_X₂ : fixSp (X₂ F) = perp (pt₀ F) := fixSp_xPoint isPoint_pt₀

end CFSG.Quasithin.MS93.MSP
end
