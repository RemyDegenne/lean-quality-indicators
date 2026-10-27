public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx

open CFSG.ClassicalInvolution.Balance

section Models

theorem isSimple_of_psp {Q : Type} [Group Q] (h : CFSG.Blueprint.LieModel Q .PSp 3 2 1) :
    IsSimpleGroup Q :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

end Models
end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
end
