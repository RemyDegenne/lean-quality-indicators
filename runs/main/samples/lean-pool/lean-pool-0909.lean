@[expose] public section

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace Spherical

section

open scoped BigOperators

namespace HigherYoungArbitraryRowDownstreamMembership

open MetricCodes.Spherical.HigherHarmonicYoung

open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex

open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

open MetricCodes.Spherical.HigherYoungArbitraryRowDownstreamCorrection

theorem downstreamCorrectedDerivative_mem_traceFree
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) lam) (k : Fin n)
    (i : Fin (r + 1)) :
    downstreamCorrectedDerivative lam a p k i ∈
      traceFreeSubmodule r n := by
  induction i using
      (measure (fun j : Fin (r + 1) => r + 1 - j.val)).wf.induction with
  | h i ih =>
    rw [downstreamCorrectedDerivative_eq]
    apply (traceFreeSubmodule r n).add_mem
      (internalRowDerivative_mem_traceFree lam i p k)
    apply Submodule.sum_mem
    intro j _
    split_ifs with hij
    · apply (traceFreeSubmodule r n).smul_mem
      apply polarization_mem_traceFreeSubmodule j i
      apply ih j
      change r + 1 - j.val < r + 1 - i.val
      have hji : i.val < j.val := hij
      have hjbound : j.val < r + 1 := j.isLt
      omega
    · exact (traceFreeSubmodule r n).zero_mem

end HigherYoungArbitraryRowDownstreamMembership
end
end Spherical
end MetricCodes
end MetricCodesNoncomputable
end
