public section

noncomputable section

open CategoryTheory Limits Topology Topology.RelCWComplex

universe w v u

namespace TauCeti

variable {X Y : Type w} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]
  {D : Set X} {E : Set Y}
  (C : Set X) [RelCWComplex C D] (C' : Set Y) [RelCWComplex C' E]

variable {f : TopCat.of C ⟶ TopCat.of C'} (hf : IsCellular C C' f)

/-- A cellular map restricts to each skeleton relative to the base. -/
def skeletonBasePairMap (n : ℕ) : skeletonBasePair C n ⟶ skeletonBasePair C' n :=
  TopPair.ofHom (skeletonMap C C' hf (n + 1)) (skeletonMap C C' hf 0)
    (skeletonMap_comp_inclusion C C' hf (Nat.zero_le (n + 1)))

end TauCeti
end
end
