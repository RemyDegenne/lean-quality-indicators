public section

namespace CFSG.Sporadic.Fi24.Native

open Matrix CFSG.F3.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem canonRows_transposeW (R : Array W) : canonRows 781 (transposeW 253 781 R) = true :=
  canonRows_of (transposeW_size _ _ _) (RowsWF.transposeW (by norm_num) _ _)
    ((zeroFrom_transposeW R).mono (by norm_num))

end CFSG.Sporadic.Fi24.Native
end
