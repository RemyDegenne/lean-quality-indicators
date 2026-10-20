@[expose] public section

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph

open Utilities.Certificate.SubdivisionGraph.Spec

theorem marks_ne_of_allSubmodular_banana
    {g : ℕ} (hg : 1 ≤ g) (B : Banana g) (u v : B.graph.V)
    (hSub : AllSubmodular (mark B.graph u v)) : u ≠ v := by
  intro huv
  subst v
  have hNonneg := (allSubmodular_iff_rankDelta_nonneg _).mp hSub (oneChip u)
  have hNeg := rankDelta_one_chip_self_lt_zero hg B u
  omega

end Bananas
end
