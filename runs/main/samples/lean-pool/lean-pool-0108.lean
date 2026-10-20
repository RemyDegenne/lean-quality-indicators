section

@[expose] public section

noncomputable section

namespace NavierStokes.PolarCharts

open Set Filter Function

open scoped ContDiff Topology BigOperators

theorem chart_finiteJets_uniform {a : ℝ} (ha : 0 < a) (b : ℝ) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : Index, ∀ k ≤ m, ∀ p ∈ Metric.closedBall (0 : Plane) b,
      ‖iteratedFDeriv ℝ k (chart a j) p‖ ≤ C := by
  have hbound (i : Index × Fin (m + 1)) : ∃ C : ℝ,
      ∀ p ∈ Metric.closedBall (0 : Plane) b,
        ‖iteratedFDeriv ℝ (i.2 : ℕ) (chart a i.1) p‖ ≤ C :=
    (isCompact_closedBall (0 : Plane) b).exists_bound_of_continuousOn
      (((chart_contDiff ha i.1).continuous_iteratedFDeriv (nat_le_smooth i.2)).continuousOn)
  choose B hB using hbound
  refine ⟨1 + ∑ i : Index × Fin (m + 1), |B i|, ?_, ?_⟩
  · have hs : 0 ≤ ∑ i : Index × Fin (m + 1), |B i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith only [hs]
  · intro j k hk p hp
    let i : Index × Fin (m + 1) := (j, ⟨k, by omega⟩)
    have hs : |B i| ≤ ∑ v : Index × Fin (m + 1), |B v| :=
      Finset.single_le_sum (fun v _ => abs_nonneg (B v)) (Finset.mem_univ i)
    exact (hB i p hp).trans ((le_abs_self (B i)).trans (by linarith only [hs]))

end NavierStokes.PolarCharts
end
end
end
