public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6X

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Uniform.U4

open scoped commutatorElement

section Branch

theorem fusion3MinBranch_of_all (h : Fusion3MinAll) : Fusion3MinBranch :=
  fun G _ _ _ _ _ hb => fusion3MinOn_of_min _ (h G hb.nonabelian)

end Branch
end CFSG.ClassicalInvolution.Q3.Q3T6X
end
