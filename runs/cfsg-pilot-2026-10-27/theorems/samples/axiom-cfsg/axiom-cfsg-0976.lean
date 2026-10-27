public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.Cover CFSG.Blueprint
  CFSG.QuasithinUnique CFSG.KC.SLD2 CFSG.QuasithinUnique.K1.SporadicPerm

open CFSG.EvenSporadicStandard.TwoCo1 (epsMask eMaskA)

open CFSG.KD.Co1K105 (letterOK)

open CFSG.Sporadic.Co1Schreier.Native (Rows)

theorem els_take : els.take CFSG.KD.Co1K105.C.ns = (List.range 15).map fun l => psi (gC l) := by
  show ((List.range 17).map fun l => qHom.rangeRestrict (xL l)).take 15 = _
  rw [← List.map_take, List.take_range, show min 15 17 = 15 from rfl]
  refine List.map_congr_left fun l hl => ?_
  show qHom.rangeRestrict (xL l) = qHom.rangeRestrict (chiC (gC l))
  rw [xL, if_pos (List.mem_range.1 hl)]

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.Co1K
end
