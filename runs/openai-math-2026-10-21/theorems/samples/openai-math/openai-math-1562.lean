namespace OAI

open Set Metric MeasureTheory

open scoped NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X]

theorem radialPowerRep_bounds {n r R : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hrR : r ≤ R) (c x : X) :
    0 ≤ radialPowerRep n r R c x ∧
      radialPowerRep n r R c x ≤ (r ^ (-n) - R ^ (-n)) / n := by
  have hm : Monotone (radialPowerPrimitive n r R) :=
    monotone_of_hasDerivAt_nonneg (fun s => radialPowerPrimitive_hasDerivAt n R s hr)
      (fun s => (radialPowerWeight_bounds hn hr s).1)
  have ht0 : 0 ≤ positiveClip (R - r) (inwardDistance c R x) :=
    le_min (le_max_right _ _) (sub_nonneg.mpr hrR)
  have htt : positiveClip (R - r) (inwardDistance c R x) ≤ R - r := min_le_right _ _
  constructor
  · change 0 ≤ radialPowerPrimitive n r R (positiveClip (R - r) (inwardDistance c R x))
    simpa only [radialPowerPrimitive_zero] using hm ht0
  · have he := radialPowerPrimitive_formula hn hr (sub_nonneg.mpr hrR) le_rfl
    rw [sub_sub_cancel] at he
    exact (hm htt).trans_eq he

end RegularPointCoordinates
end
end OAI
