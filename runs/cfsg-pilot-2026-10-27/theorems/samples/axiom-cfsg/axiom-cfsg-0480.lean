public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.TwoA Native Matrix

open CFSG.Monster.B.Co2 (v0 qbW qbWBasis qbWBasis_apply decW decW_xor decW_zero decW_eq_equivFun
  genQuotMatrix)

open CFSG.Monster.B.TwoA.Co2Inv (rK rK_mul_self rK_ne_one wAct_rK rowsEnd_qbW decW_one_shiftLeft
  ncard_conjClass_rK)

open CFSG.Sporadic.Co2Inv (co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem rkW_rKS :
    rkW rKS = 6 := by
  rw [rkW, ← finrank_wAct_congr hv0 rKS rK rfl, finrank_range_rK]

end CFSG.Monster.B.CTIB
end
