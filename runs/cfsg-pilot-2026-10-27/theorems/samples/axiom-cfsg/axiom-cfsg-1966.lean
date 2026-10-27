public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

attribute [local irreducible] pairMat linePair

section Lift

variable {k : ℕ} (h : TsPair (dec12 (linePair k).1) (dec12 (linePair k).2))

include h

theorem colsLin_tvCols_invol (v : V) : colsLin (tvCols k) (colsLin (tvCols k) v) = v := by
  apply exL_injective
  rw [exL_colsLin_tvCols, exL_colsLin_tvCols, tlift_apply_tlift h]

end Lift
end CFSG.GF2Type.SmithTypeE.DMod
end
