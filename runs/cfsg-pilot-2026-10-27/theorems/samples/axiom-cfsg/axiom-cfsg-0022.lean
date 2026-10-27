public noncomputable section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG CFSG.LocalCores CFSG.Blueprint CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Monster.B.Co2

open CFSG.Monster.B.Co2.Native CFSG.LocalAnalysis.ComponentInitial

open scoped Pointwise

theorem card_heInnerGrp1 :
    Nat.card heInnerGrp1 = 21504 := by
  rw [heInnerGrp1_eq, card_heP_cent1]

end CFSG.Sporadic.SmallOddCore
end
