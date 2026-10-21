namespace OAI

section

namespace PerfectCompleteness.CutCallExtension

open scoped Classical

open TreeSourceSpaces HierarchicalArrays PointwiseSpaces

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

theorem observe_law :
    (CutChildGrouping.rawLaw (C := Option C) slots rows).pushforward
        (observe slots rows) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := C) slots rows)).product
        (FiniteDistribution.uniform (H slots)) := by
  change (CutChildGrouping.rawLaw (C := Option C) slots rows).pushforward
    (fun x => splitAssembled slots rows (CutChildGrouping.assemble slots rows x)) = _
  rw [← FiniteDistribution.pushforward_comp, CutChildGrouping.assemble_law,
    UniformLinearImage.uniform_pushforward_linearMap
      (splitAssembled slots rows) (splitAssembled_surjective slots rows)]
  exact WholeCutSampler.uniform_product.symm

end
end PerfectCompleteness.CutCallExtension
end
end OAI
