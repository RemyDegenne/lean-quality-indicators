public section

noncomputable section

open Set Function TopologicalSpace Filter ENNReal Metric

open scoped Topology

namespace Metric

variable {α : Type*} [PseudoEMetricSpace α]

/-- The Hausdorff pseudo emetric on the powerset of a pseudo emetric space.
See note [reducible non-instances]. -/
protected abbrev _root_.PseudoEMetricSpace.hausdorff : PseudoEMetricSpace (Set α) where
  edist s t := hausdorffEDist s t
  edist_self _ := hausdorffEDist_self
  edist_comm _ _ := hausdorffEDist_comm
  edist_triangle _ _ _ := hausdorffEDist_triangle
  toUniformSpace := .hausdorff α
  uniformity_edist := by
    refine le_antisymm
      (le_iInf₂ fun ε hε => Filter.le_principal_iff.mpr ?_)
      (uniformity_basis_edist.lift' monotone_hausdorffEntourage |>.ge_iff.mpr fun ε hε =>
        Filter.mem_iInf_of_mem ε <| Filter.mem_iInf_of_mem hε fun _ =>
        mem_hausdorffEntourage_of_hausdorffEDist_lt)
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    filter_upwards [Filter.mem_lift' (uniformity_basis_edist_le.mem_of_mem hδ)]
      with _ h using hδε.trans_le' <| hausdorffEDist_le_of_mem_hausdorffEntourage h

end Metric
end
end
