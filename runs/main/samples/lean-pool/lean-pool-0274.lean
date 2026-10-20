@[expose] public section

open Metric Set

namespace Schoenflies

namespace Plane

theorem beyondSquare_eq_compl (r : ℝ) : beyondSquare r = (closedSquare 0 r)ᶜ := by
  ext x
  simp only [beyondSquare, closedSquare, Set.mem_ofPred_eq, mem_compl_iff, supDist_zero, supNorm,
    max_le_iff, not_and_or, not_le]

end Plane
end Schoenflies
end
