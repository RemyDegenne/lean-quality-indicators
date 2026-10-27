public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA

theorem wFr_mem_commV :
    wFr ∈ commV := by
  have h1 := n6vec_add_wFr_mem 1
  have h3 := n6vec_add_wFr_mem 3
  have e : wFr = (n6vec 1 + wFr) + (n6vec 3 + wFr) := by
    have hs := n6vec_sum_zero
    rw [n6vec_zero] at hs
    calc wFr = wFr + (wFr + n6vec 1 + n6vec 3) := by rw [hs, add_zero]
      _ = (n6vec 1 + wFr) + (n6vec 3 + wFr) := by
        have hw := add_self_W wFr
        calc wFr + (wFr + n6vec 1 + n6vec 3) = (wFr + wFr) + n6vec 1 + n6vec 3 := by abel
          _ = n6vec 1 + n6vec 3 := by rw [hw, zero_add]
          _ = (n6vec 1 + wFr) + (n6vec 3 + wFr) := by
            rw [add_add_add_comm, hw, add_zero]
  rw [e]
  exact commV.add_mem h1 h3

end CFSG.Monster.B.TwoA.Unitary
end
