@[expose] public section

universe u v w

open CategoryTheory ContRepresentation TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [CompactSpace G]

/-- Swap two successive coinduced evaluation arguments. -/
def swapCoind (Y : TopRep.{max v w} k G) [DiscreteTopology Y] :
    Y.ρ.coind₁.coind₁ →ⁱL Y.ρ.coind₁.coind₁ where
  toFun f := ContinuousMap.curry
    ⟨fun p : G × G => f p.2 p.1,
      continuous_eval.comp ((f.continuous.comp continuous_snd).prodMk continuous_fst)⟩
  map_add' f f' := by ext g t; rfl
  map_smul' scalar f := by ext g t; rfl
  cont := by
    let : DiscreteTopology C(G, Y) := ContinuousMap.discreteTopology_of_compactSpace
    let : DiscreteTopology C(G, C(G, Y)) :=
      ContinuousMap.discreteTopology_of_compactSpace
    exact continuous_of_discreteTopology
  isIntertwining' g := by
    ext f h t
    simp [ContinuousMap.curry_apply, ContRepresentation.coind₁_apply_apply]

end ContinuousCohomology
end
