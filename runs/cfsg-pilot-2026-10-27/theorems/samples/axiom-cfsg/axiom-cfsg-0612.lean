public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup CFSG.Fischer CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem fld_fld (g : SU52) : fld (fld g) = g := fldFun_fldFun g

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
end
