public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix CFSG.Fischer

theorem toMat_reBits_one : toMat 8 8 (reBits fun i j => if i = j then 1 else 0) = 1 := by
  decide

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
end
