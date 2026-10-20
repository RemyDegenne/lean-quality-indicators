@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace NavierStokes.MeanRankUpdate

open Set Function MeasureTheory Filter

open scoped BigOperators ContDiff Topology

section RankClass

theorem rank_update_meanClass (s : WeightedClasses.StripData ChartPoint)
    {coord A B lam a b qlo qhi rlo rhi α : ℝ} (hc : 0 < coord) (hc1 : coord < 1)
    (ha : 0 < a) (hab : a < b) (hB : B ≠ 0) (hqlo : 0 < qlo)
    (hT : ∀ p ∈ s.domain, chartInput p ∈ PhysicalCoordinateBounds.positiveTime)
    (hq : ∀ p ∈ s.domain, chartQ coord p ∈ Icc qlo qhi)
    (hR : ∀ p ∈ s.domain, p.1 ∈ Icc rlo rhi)
    (hz : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ s.domain, p ∈ supportBand a b qlo qhi → δ ≤ s.zeta p)
    {d : ℕ → ChartPoint → Debt} (hd : WeightedClasses.UnweightedClass s α d) :
    WeightedClasses.MeanClass s α (fun n => chartAngular coord A B lam a b (d n)) ∧
      WeightedClasses.MeanClass s α (fun n => chartAxial coord A B lam a b (d n)) := by
  have hk (i : Fin 3) := rank_kernels_meanClass (A := A) (B := B) (lam := lam) s
    hc hc1 ha hab hB hqlo hT hq hR hz (Pi.single i 1)
  have hcoord (i : Fin 3) : WeightedClasses.UnweightedClass s α (fun n p => d n p i) :=
    hd.map (ContinuousLinearMap.proj i)
  constructor
  · have ht (i : Fin 3) : WeightedClasses.MemClass s (fun _ p => s.zeta p) α
        (fun n p => d n p i * chartKernel coord (angularModel coord A B lam a b (Pi.single i 1)) p)
            := by
      simpa only [add_zero, one_mul] using (hcoord i).mul (hk i).1
    have hs := WeightedClasses.MemClass.sum Finset.univ _
      (fun _ p hp => s.zeta_nonneg p hp) (fun i _ => ht i)
    have he : (fun n => chartAngular coord A B lam a b (d n)) =
        (fun n p => ∑ i : Fin 3, d n p i *
          chartKernel coord (angularModel coord A B lam a b (Pi.single i 1)) p) := by
      funext n p
      exact chartAngular_eq_sum _ _ _ _ _ _ _ _
    rw [he]
    exact hs
  · have ht (i : Fin 3) : WeightedClasses.MemClass s (fun _ p => s.zeta p) α
        (fun n p => d n p i * chartKernel coord (axialModel coord A B lam a b (Pi.single i 1)) p)
            := by
      simpa only [add_zero, one_mul] using (hcoord i).mul (hk i).2
    have hs := WeightedClasses.MemClass.sum Finset.univ _
      (fun _ p hp => s.zeta_nonneg p hp) (fun i _ => ht i)
    have he : (fun n => chartAxial coord A B lam a b (d n)) =
        (fun n p => ∑ i : Fin 3, d n p i *
          chartKernel coord (axialModel coord A B lam a b (Pi.single i 1)) p) := by
      funext n p
      exact chartAxial_eq_sum _ _ _ _ _ _ _ _
    rw [he]
    exact hs

end RankClass
end NavierStokes.MeanRankUpdate
end
end
