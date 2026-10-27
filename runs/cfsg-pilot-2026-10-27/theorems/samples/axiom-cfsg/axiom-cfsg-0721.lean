public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

theorem natCard_Cfull : Nat.card Cfull = 2 * Nat.card Dfull := by
  have h2 : Nat.card ZstarF = 2 := by rw [ZstarF, Nat.card_zpowers, orderOf_tStarF]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ZstarF, h2, mul_comm]

end CFSG.Monster.B.TwoA
end
