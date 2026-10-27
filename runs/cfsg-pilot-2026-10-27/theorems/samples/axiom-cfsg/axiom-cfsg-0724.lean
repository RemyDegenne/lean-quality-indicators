public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

open Matrix Matrix.ProjGenLinGroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag UnitaryHigher

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)

section Reindex

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r ε : ℕ}
  {κ : Type} [Fintype κ] [DecidableEq κ] (e : HypIndex r ε ≃ κ)

theorem reindex_hypGram_mul_self :
    reindex e e (hypGram r ε K) * reindex e e (hypGram r ε K) = 1 := by
  rw [← coe_reindexAlgEquiv K K e, ← map_mul, hypGram_mul_self, map_one]

end Reindex
end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
end
