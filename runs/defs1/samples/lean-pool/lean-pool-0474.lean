noncomputable section

namespace SoficGroups

section

open Filter Topology

universe u v w

open scoped Pointwise commutatorElement symmDiff

/-- Internal interface connecting the split non-sofic proof modules. -/
public
structure ExpandingCentralizerFiniteModel (G : Type*) [Group G]
    (F : Finset G) where
  /-- Internal interface connecting the split non-sofic proof modules. -/
  vertices : Type
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [verticesFintype : Fintype vertices]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [verticesDecidableEq : DecidableEq vertices]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  generatorIndex : Type
  /-- Internal interface connecting the split non-sofic proof modules. -/
  [generatorFintype : Fintype generatorIndex]
  /-- Internal interface connecting the split non-sofic proof modules. -/
  generators : generatorIndex → Equiv.Perm vertices
  /-- Internal interface connecting the split non-sofic proof modules. -/
  tolerance : ℕ
  /-- Internal interface connecting the split non-sofic proof modules. -/
  cheeger : ℝ
  cheeger_positive : 0 < cheeger
  expansion : ∀ A : Finset vertices,
    cheeger * min (A.card : ℝ)
        ((Fintype.card vertices : ℝ) - A.card) ≤
      (boundary generators A : ℝ)
  small : (10 : ℝ) * tolerance < cheeger * Fintype.card vertices
  /-- Internal interface connecting the split non-sofic proof modules. -/
  repair : AlmostCentralizerRepair generators tolerance
  /-- Internal interface connecting the split non-sofic proof modules. -/
  approximation : G → AlmostCentralizerElement generators tolerance
  map_one : (approximation 1).permutation = 1
  multiplicative : ∀ x ∈ F, ∀ y ∈ F,
    5 * permutationDistance (approximation (x * y)).permutation
      ((approximation x).permutation * (approximation y).permutation) ≤
        Fintype.card vertices
  separated : ∀ x ∈ F, ∀ y ∈ F, x ≠ y →
    Fintype.card vertices <
      5 * permutationDistance
        (approximation x).permutation (approximation y).permutation

end
end SoficGroups
end
