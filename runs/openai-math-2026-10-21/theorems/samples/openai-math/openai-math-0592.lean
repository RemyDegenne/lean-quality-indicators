namespace OAI

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical

open SmallContextCoordinates SmallContextEnumeration SmallContextFibres

open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox

open IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles

open FirstPaperContextTransport FirstPaperPhysicalMarginal FiniteExposureVariance

open PaddedCompletions CompletionCounts

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma physicalContextEnergy_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (s : I×J) (σ : I×J → ℕ) (f H : SmallProfile small → ℝ) (hf : ∀ z,0 ≤ f z) :
    0 ≤ physicalContextEnergy small B s σ f H := by
  unfold physicalContextEnergy
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _))

end ContingencyTables.SmallGraphProfiles
end OAI
