public section

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

theorem colsLin_single (cols : Array Nat) (m : Fin 32) :
    colsLin cols (Pi.single m 1) = decode32 cols[m.val]! := by
  rw [colsLin_apply, Finset.sum_eq_single m]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

end CFSG.GF2Type.SmithTypeE.DMod
end
