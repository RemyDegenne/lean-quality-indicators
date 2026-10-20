@[expose] public section

open Metric Set

open scoped Graph

namespace Schoenflies

variable {F : Set Plane} {a b y : Plane}

theorem localGridEdges_nondeg {p : Plane} {s : ℝ} {k : ℕ} (hs : 0 < s) (hk : 1 ≤ k) :
    ∀ P ∈ localGridEdges p s k, P.Nondeg := fun _ hP =>
  gridEdges_nondeg ((localGridX_strictMono hs hk).strictMonoOn _)
    ((localGridY_strictMono hs hk).strictMonoOn _) hk hk hP

end Schoenflies
end
