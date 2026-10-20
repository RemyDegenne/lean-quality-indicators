public section

noncomputable section

open Set Metric Complex Real

namespace TauCeti

namespace ThricePuncturedSphere

theorem isPathConnected_puncturedNeighborhoodZero : IsPathConnected puncturedNeighborhoodZero := by
  have := pathConnectedSpace_ball_diff_singleton (0 : ℂ) (R := 1 / 2) (by norm_num)
  exact isPathConnected_iff_pathConnectedSpace.2 (ballHomeomorph
    mem_puncturedNeighborhoodZero_iff_mem_ball
    (ball_diff_subset_range (.inl rfl) (by norm_num))).symm.pathConnectedSpace

end ThricePuncturedSphere
end TauCeti
end
end
