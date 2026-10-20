@[expose] public section

namespace ThreeGap.EuclideanRecords

open scoped Real

open ThreeGap.SimApprox ThreeGap.Chevallier

theorem dstar3 : deltaN (euclNorm 2) astar 3 = Real.sqrt 106 / 29 := by
  rw [deltaN_astar 3 0 1 9 (-5) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; norm_num

end ThreeGap.EuclideanRecords
end
