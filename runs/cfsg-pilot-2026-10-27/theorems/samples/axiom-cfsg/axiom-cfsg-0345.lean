public section

namespace CFSG.ComponentClassification.RankTwoClassical.ExcO8E

open Subgroup CFSG.ComponentClassification.RankTwoClassical.ExcO8

open CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native

open CFSG.Monster.B.Co2 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl

open CFSG.EvenSmallLie.OmegaEight.Cover

theorem s48_eq :
    s48 = Subgroup.closure {g | g ∈ s48Words.map fun w => tab (evalCodes seGens w)} := by
  rw [s48, s48Q, certificate_originalSubgroup]
  rfl

end CFSG.ComponentClassification.RankTwoClassical.ExcO8E
end
