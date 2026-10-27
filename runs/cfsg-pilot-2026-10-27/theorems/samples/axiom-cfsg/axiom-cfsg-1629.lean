@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

theorem tvG_mem_sp0 (v : Fin 6 → ZMod 2) : tvG v ∈ Sp0 :=
  sp_tvM_mem v

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
end
