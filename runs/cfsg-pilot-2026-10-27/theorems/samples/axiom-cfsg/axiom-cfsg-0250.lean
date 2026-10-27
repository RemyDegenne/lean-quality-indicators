public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin CFSG.Quasithin.H13 Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem normG_eq :
    normG = m22P :=
  (Subgroup.eq_of_le_of_card_ge m22P_le_normG (by rw [card_m22P]; exact card_normG_le)).symm

end CFSG.Quasithin.H.Mathieu.M22Link
end
