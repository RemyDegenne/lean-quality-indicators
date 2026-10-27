public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaD

theorem toMat_Pinv_mul : toMat 8 8 PinvBits * toMat 8 8 PBits = 1 := by
  rw [← toMat_bmul, thetaCheck_parts.2.1, toMat_id8]

end CFSG.EvenSmallLie.UnitarySix.Child5
end
