public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTableBActionInputOn_linTwo_holds : GGTableBActionInputOn GGLinTwoLabel :=
  ggTableBActionInputOn_of_labelsSCr ggBstarInnerDiagLInputOn_linTwo
    fun _ _ _ _ h => largeEvenLabelAll_linTwo_action h

end CFSG.StandardType
end
