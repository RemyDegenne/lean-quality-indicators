@[expose] public section

noncomputable section PortComputability

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology

namespace MarkovProcess

namespace ContinuousPath

section

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Frontier

theorem coordinate_exitTime_mem_frontier (U : Set alpha) (hU : IsOpen U)
    (omega : ContinuousPath alpha) (h0 : omega 0 ∈ U) (hfin : exitTime U omega ≠ ⊤) :
    omega ((exitTime U omega).toNNReal) ∈ frontier U := by
  set tau : NNReal := (exitTime U omega).toNNReal with htau
  have hcoe : (tau : ℝ≥0∞) = exitTime U omega := ENNReal.coe_toNNReal hfin
  have hbefore : ∀ s : NNReal, s < tau → omega s ∈ U := by
    intro s hs
    apply mem_of_lt_exitTime
    rw [← hcoe, ENNReal.coe_lt_coe]
    exact hs
  have hnot : omega tau ∉ U := by
    obtain ⟨s, hs⟩ :=
      (exitTime_le_iff_mem_hitsSetBy U hU tau omega).mp (le_of_eq hcoe.symm)
    have hge : tau ≤ (s : NNReal) := by
      by_contra hlt
      exact hs (hbefore s (lt_of_not_ge hlt))
    have hseq : (s : NNReal) = tau := le_antisymm s.property hge
    rw [← hseq]
    exact hs
  have htau0 : tau ≠ 0 := by
    intro h
    rw [h] at hnot
    exact hnot h0
  have hclosure : omega tau ∈ closure U := by
    have hnebot : (nhdsWithin tau (Set.Iio tau)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ tau) (Ne.symm htau0)⟩
    have htend : Filter.Tendsto (omega : NNReal → alpha) (nhdsWithin tau (Set.Iio tau))
        (nhds (omega tau)) := (omega.continuous.tendsto tau).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbefore s hs
  rw [hU.frontier_eq]
  exact ⟨hclosure, hnot⟩

end Frontier
end
end ContinuousPath
end MarkovProcess
end PortComputability
end
