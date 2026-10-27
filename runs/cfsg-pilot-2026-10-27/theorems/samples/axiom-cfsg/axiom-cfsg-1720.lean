public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne.KCSpFull

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

variable {ℓ f p : ℕ} {Ahat : Subgroup (StatedSp r K)}

theorem SpPlaneSetupQ.not_exceptional (S : SpPlaneSetupQ ℓ f p r K Ahat) :
    ¬ (r = 2 ∧ ℓ ^ f = 2) := fun h => by
  have := S.four_le_q
  omega

end CFSG.HardMathSupport.Timmesfeld.CrossChar
end
