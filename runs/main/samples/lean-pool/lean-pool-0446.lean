@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral

namespace AVenhance.Infra.Section5.RelativeError

theorem TraceAveraging.intervalIntegral_f_le_sqrt_length_mul_l2
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ s in (0 : ℝ)..t, f s) ≤
      Real.sqrt t * Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2) := by
  let I : Set ℝ := Set.Ioc (0 : ℝ) t
  have hsubset : I ⊆ Set.Icc (0 : ℝ) t := by
    intro x hx
    exact ⟨hx.1.le, hx.2⟩
  have hfIcc : ContinuousOn f (Set.Icc (0 : ℝ) t) := hf.mono (by
    intro x hx
    exact ⟨hx.1, le_trans hx.2 ht1⟩)
  have hfI : IntegrableOn f I := by
    exact (hfIcc.integrableOn_compact isCompact_Icc).mono_set hsubset
  have hf2I : IntegrableOn (fun x => f x ^ 2) I := by
    exact ((hfIcc.pow 2).integrableOn_compact isCompact_Icc).mono_set hsubset
  have honeI : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I := by
    exact (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set hsubset
  have honeSqI : IntegrableOn (fun x : ℝ => (1 : ℝ) ^ 2) I := by
    simpa using honeI
  have hprodI : IntegrableOn (fun x => f x * 1) I := by
    simpa using hfI
  have hcs := AVenhance.Infra.Section5.LeftToShow.integral_mul_le_sqrt_mul_sqrt
    (μ := volume.restrict I) (f := f) (g := fun _ : ℝ => (1 : ℝ))
    hf2I honeSqI hprodI
  have hcsSimple :
      (∫ x in I, f x) ≤
        Real.sqrt (∫ x in I, f x ^ 2) * Real.sqrt (∫ x in I, (1 : ℝ)) := by
    simpa using hcs
  have hfconv :
      (∫ x in I, f x) = (∫ s in (0 : ℝ)..t, f s) := by
    dsimp [I]
    exact (intervalIntegral.integral_of_le ht0).symm
  have hsqconv :
      (∫ x in I, f x ^ 2) = (∫ s in (0 : ℝ)..t, f s ^ 2) := by
    dsimp [I]
    exact (intervalIntegral.integral_of_le ht0).symm
  have honeconv : (∫ x in I, (1 : ℝ)) = t := by
    calc
      (∫ x in I, (1 : ℝ)) =
          (∫ s in (0 : ℝ)..t, (1 : ℝ)) :=
        (intervalIntegral.integral_of_le ht0).symm
      _ = t := by simp [intervalIntegral.integral_const]
  have hcs' :
      (∫ s in (0 : ℝ)..t, f s) ≤
        Real.sqrt (∫ s in (0 : ℝ)..t, f s ^ 2) * Real.sqrt t := by
    rw [← hfconv, ← hsqconv, ← honeconv]
    exact hcsSimple
  have hG : IntervalIntegrable (fun s : ℝ => f s ^ 2) volume 0 1 :=
    (hf.pow 2).intervalIntegrable_of_Icc zero_le_one
  have hleft : IntervalIntegrable (fun s : ℝ => f s ^ 2) volume 0 t :=
    hG.mono_set (by
      rw [Set.uIcc_of_le ht0, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc_right ht1)
  have hright : IntervalIntegrable (fun s : ℝ => f s ^ 2) volume t 1 :=
    hG.mono_set (by
      rw [Set.uIcc_of_le ht1, Set.uIcc_of_le zero_le_one]
      exact Set.Icc_subset_Icc_left ht0)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hrest : 0 ≤ (∫ s in t..1, f s ^ 2) :=
    intervalIntegral.integral_nonneg ht1 (fun s hs => sq_nonneg (f s))
  have hsqmono :
      (∫ s in (0 : ℝ)..t, f s ^ 2) ≤
        (∫ s in (0 : ℝ)..1, f s ^ 2) := by
    rw [← hadd]
    linarith
  calc
    (∫ s in (0 : ℝ)..t, f s) ≤
        Real.sqrt (∫ s in (0 : ℝ)..t, f s ^ 2) * Real.sqrt t := hcs'
    _ ≤ Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2) * Real.sqrt t := by
      exact mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt hsqmono) (Real.sqrt_nonneg _)
    _ = Real.sqrt t * Real.sqrt (∫ s in (0 : ℝ)..1, f s ^ 2) := by ring

end AVenhance.Infra.Section5.RelativeError
end
end
