@[expose] public section

namespace Homogenization

theorem cubeBoundaryLayer_subset_cubeSet {d : ℕ} (Q : TriadicCube d) (t : ℝ) :
    cubeBoundaryLayer Q t ⊆ cubeSet Q :=
  Set.sdiff_subset

end Homogenization
end
