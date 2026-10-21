namespace OAI

noncomputable section

universe u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12

open Complex Metric Set Filter Real

open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter

open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter

open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter

open scoped Topology ComplexConjugate

open Set Filter Metric

open scoped Topology

open Set Filter Metric Complex

open scoped Topology

open Set Filter Metric Complex

open scoped Topology

open Set Metric Filter Topology

open Set Metric Filter Topology

open Set Filter Topology Complex

open Set Filter Metric Complex

open scoped Topology ComplexConjugate

namespace CompleteCrouzeix

open Set Metric Filter Complex

open scoped Topology BigOperators ComplexConjugate

lemma convexBarrier_sublevel_convex {ι : Type u_9} [Fintype ι] {c : ℝ} (hc : 0 ≤ c)
    (l : ι → ℂ →L[ℝ] ℝ) (a : ι → ℝ) :
    Convex ℝ {z | convexBarrier c l a z < 1} := by
  simpa using (convexBarrier_convex hc l a).convex_lt 1

end CompleteCrouzeix
end
end OAI
