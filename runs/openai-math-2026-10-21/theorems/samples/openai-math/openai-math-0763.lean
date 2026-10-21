namespace OAI

open MeasureTheory ProbabilityTheory

open scoped ENNReal

open scoped RealInnerProductSpace

open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal RealInnerProductSpace

open Filter

open scoped Topology

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology

open scoped RealInnerProductSpace

open Set Filter

open scoped Topology RealInnerProductSpace

open scoped NNReal

open Set Filter

open scoped Topology RealInnerProductSpace NNReal

open MeasureTheory ProbabilityTheory Set Filter

open scoped Topology RealInnerProductSpace

open MeasureTheory Set Filter

open scoped Topology BigOperators

open MeasureTheory ProbabilityTheory Set Filter

open scoped RealInnerProductSpace Topology

open MeasureTheory ProbabilityTheory Set Filter

open scoped RealInnerProductSpace Topology ENNReal

open MeasureTheory ProbabilityTheory Set Filter

open scoped RealInnerProductSpace Topology ENNReal

open Metric

open MeasureTheory ProbabilityTheory Set

open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourCertificates

open OneCell ProbabilityBounds Mills Taylor

lemma large_4 {r x:ℝ} (hr:r∈Icc (41/100:ℝ) (33/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (33/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (41973/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (41973/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (33/80:ℝ) ≤ p (41973/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (41973/50000:ℝ)≤(6269/31250:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (41973/50000:ℝ)≤(349543/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (41973/50000:ℝ)≤(97647/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/100:ℝ)) (q:=(41973/50000:ℝ)) (v:=(880833/1000000:ℝ))
    (u:=(6269/31250:ℝ)^2*(97647/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

end GaussianPropeller.FourCertificates
end OAI
