public section

noncomputable section

open Filter MeasureTheory Set Topology

open scoped ENNReal NNReal Interval

namespace TauCeti

section LowerSemicontinuous

variable {X : Type*} [PseudoMetricSpace X] {p : ℝ} {γ : ℝ → X} {a b : ℝ} {ι : Type*}
  {l : Filter ι} {γs : ι → ℝ → X}

theorem absolutelyContinuousOnInterval_of_tendsto_of_liminf_ne_top (hp : 1 < p)
    (hγs : ∀ᶠ i in l, AbsolutelyContinuousOnInterval (γs i) a b)
    (hlim : ∀ t ∈ uIcc a b, Tendsto (fun i ↦ γs i t) l (𝓝 (γ t)))
    (hA : liminf (fun i ↦ curveAction p (γs i) a b) l ≠ ∞) :
    AbsolutelyContinuousOnInterval γ a b := by
  obtain ⟨C, hAC, hC⟩ := exists_between (lt_top_iff_ne_top.2 hA)
  have hfreq : ∃ᶠ i in l, curveAction p (γs i) a b < C := frequently_lt_of_liminf_lt
    (by isBoundedDefault) hAC
  -- The Hölder estimate on the union of the intervals bounds the distances along `γ`.
  refine absolutelyContinuousOnInterval_of_sum_edist_rpow_le hp hC.ne ?_
  rintro ⟨k, I⟩ hE
  have hsum : Tendsto (fun i ↦ (∑ j ∈ Finset.range k, edist (γs i (I j).1) (γs i (I j).2)) ^ p)
      l (𝓝 ((∑ j ∈ Finset.range k, edist (γ (I j).1) (γ (I j).2)) ^ p)) :=
    (ENNReal.continuous_rpow_const.tendsto _).comp (tendsto_finsetSum _ fun j hj ↦
      (hlim _ (hE.1 j hj).1).edist (hlim _ (hE.1 j hj).2))
  exact le_of_tendsto_of_frequently hsum
    ((hfreq.and_eventually hγs).mono fun i hi ↦
      (hi.2.sum_edist_rpow_le_mul_curveAction hp.le hE).trans (by gcongr; exact hi.1.le))

end LowerSemicontinuous
end TauCeti
end
end
