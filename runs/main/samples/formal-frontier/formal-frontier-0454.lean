@[expose] public section

open CategoryTheory Convexity

open scoped BigOperators Simplicial

noncomputable section

namespace Convexity.StdSimplex

theorem AffineSimplex.face_cone_succ {m n : ℕ}
    (b : StdSimplex ℝ (Fin (m + 1))) (a : AffineSimplex m (n + 1))
    (i : Fin (n + 2)) :
    (a.cone b).face i.succ = (a.face i).cone b := by
  funext j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [AffineSimplex.face, AffineSimplex.cone]
  · simp [AffineSimplex.face, AffineSimplex.cone, Fin.succ_succAbove_succ]

end Convexity.StdSimplex
end
end
