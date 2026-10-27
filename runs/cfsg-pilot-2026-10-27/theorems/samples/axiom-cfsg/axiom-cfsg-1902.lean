public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem fi22Chain_orbitSizes :
    (List.finRange fi22Chain.baseCount).map fi22Chain.orbitSize = [3510, 2816, 567, 720, 8, 2] := by
  have h := fi22Order_check.2
  rw [rawOrbitSizes] at h
  rw [← h]
  apply List.ext_getElem
  · simp [rawLevels, fi22BaseArr, fi22ChainBase]
    rfl
  · intro k h1 h2
    have hk : k < (rawLevels 3510 fi22StrongArrs fi22BaseArr).size := by simpa using h2
    simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
    rw [fi22Chain_valid.2]
    show ((rawLevels 3510 fi22StrongArrs fi22BaseArr)[k]!).pts.size = _
    rw [getElem!_pos _ k hk]

end CFSG.Monster.B.Fischer
end
