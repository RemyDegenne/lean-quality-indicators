public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S5
  Certificates.S5Rows

section Lift

variable {G : Type*} [Group G] {i j : G}

theorem q8Lift_xa (h : Q8Rel i j) (k : ZMod (2 * 2)) :
    q8Lift h (QuaternionGroup.xa k) = j * i ^ k.val := rfl

end Lift
end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Cert
end
