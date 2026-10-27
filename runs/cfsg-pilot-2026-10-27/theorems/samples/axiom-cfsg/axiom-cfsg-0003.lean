public section

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.Open CFSG.LargeExtraspecial.Bridge Matrix

open scoped MatrixGroups

theorem timmesfeld78Co1Dvd47_of_mainStatement (hM : MainStatement) :
    Timmesfeld78Co1Dvd47 := by
  intro G _ _ _ z h47 hz hext hcard hcen hCo2
  exact nonempty_quotient_co1_of_mainStatement hM z hz hext hcard hcen hCo2
    (fun h => not_dvd_47_card_alt2 h h47)

end CFSG.EvenSporadicStandard.TwoB
end
