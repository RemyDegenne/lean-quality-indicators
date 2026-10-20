@[expose] public section

open scoped BigOperators

namespace BeyondBethe

theorem sum_cleanCycleWeightedCost_le_coreTransferCost
    {n : ℕ} {τ η : ℝ}
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hP : IsDoublyStochastic P) (hτ : 0 ≤ τ)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (f g : Equiv.Perm (Fin n)) :
    (∑ c : cleanCycleFactors η P (alternatingRowPerm f g),
        cleanCycleWeightedCost (fun i j ↦ transferU τ (X i) j) c) ≤
      coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
        (fun i j ↦ transferU τ (X i) j) := by
  let S := cleanCycleFactors η P (alternatingRowPerm f g)
  let t : (alternatingRowPerm f g).cycleFactorsFinset → Finset (Fin n) :=
    fun c ↦ (c : Equiv.Perm (Fin n)).support
  let w : Fin n → ℝ := fun i ↦ encodedCoreRowTransferCost f g P
    (fun a b ↦ transferU τ (X a) b) i
  have hpair : (↑S : Set (alternatingRowPerm f g).cycleFactorsFinset).PairwiseDisjoint t := by
    intro c hc d hd hcd
    have hcd' : (c : Equiv.Perm (Fin n)) ≠ d := by
      intro heq
      apply hcd
      exact Subtype.ext heq
    exact (alternatingRowPerm f g).cycleFactorsFinset_pairwise_disjoint
      c.2 d.2 hcd' |>.disjoint_support
  have hunion : (∑ c : S, ∑ i ∈ t c.1, w i) =
      ∑ i ∈ S.biUnion t, w i := by
    calc
      (∑ c : S, ∑ i ∈ t c.1, w i) =
          ∑ c ∈ S, ∑ i ∈ t c, w i := by
        simpa using Finset.sum_coe_sort S (fun c ↦ ∑ i ∈ t c, w i)
      _ = ∑ i ∈ S.biUnion t, w i := (Finset.sum_biUnion hpair).symm
  change (∑ c : S, cleanCycleWeightedCost
    (fun a b => transferU τ (X a) b) c) ≤ ∑ i, w i
  simp_rw [cleanCycleWeightedCost_eq_support_sum
    (fun a b => transferU τ (X a) b)]
  change (∑ c : S, ∑ i ∈ t c.1, w i) ≤ ∑ i, w i
  rw [hunion]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ ↦ encodedCoreRowTransferCost_nonneg hτ hP hXint f g i)

end BeyondBethe
end
