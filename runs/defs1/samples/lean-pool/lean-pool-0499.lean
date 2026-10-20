@[expose] public section

open Set

namespace Wallace

noncomputable section

open AlmostDisjoint

universe u v

namespace LocalCodeSchedule

open BlockData TriangularPreprocess

/-- Pairwise-disjoint refinements of the labels of all codes relevant to `D`. -/
def refinedLabel (index : ContinuumIndex ↪ ContinuumIndex)
    (D : Set ContinuumIndex) (hD : D.Countable) : RelevantCode index D → Set ℕ := by
  let : Countable (RelevantCode index D) := by exact relevantCode_countable index D hD
  exact Classical.choose
    (exists_disjoint_refinement_countable
      (fun a : RelevantCode index D ↦ label a.1) (private_decl% (relevantLabels_pairwise index D)))

end LocalCodeSchedule
end
end Wallace
end
