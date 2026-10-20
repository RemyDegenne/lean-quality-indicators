set_option warningAsError true

@[expose] public section

universe u v w

open CategoryTheory

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G)

theorem exists_common_stage_refinement (N₀ : OpenNormalSubgroup G) (i : ℕ)
    (S : Finset (TopRep.resolutionX X i))
    (hS : ∀ a ∈ S, ∃ N : OpenNormalSubgroup G, StageDescends X N i a) :
    ∃ N : OpenNormalSubgroup G, N ≤ N₀ ∧
      ∀ a ∈ S, StageDescends X N i a :=
  exists_common_refinement (fun N a => StageDescends X N i a)
    (fun h a ha => stageDescends_antitone X h i a ha) N₀ S hS

end ContinuousCohomology
end
