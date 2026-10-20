public section

namespace NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {w : InfinitePlace K}

@[simp]
theorem norm_continuousMulEquivRealOfIsReal_symm (hw : w.IsReal) (x : ℝ) :
    ‖(continuousMulEquivRealOfIsReal hw).symm x‖ = |x| :=
  (isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
    (map_zero (ringEquivRealOfIsReal hw).symm) x

end NumberField.InfinitePlace.Completion
end
