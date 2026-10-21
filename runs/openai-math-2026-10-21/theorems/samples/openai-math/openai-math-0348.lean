namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace ZeroTemperatureSK.Heat

lemma tiltedBackward_family {f g : ℝ → ℝ} {K : ℝ≥0}
    (hf : RegularDatum f) (hLip : LipschitzWith K f) (hg : BoundedSmooth g) {c : ℝ} (hc : 0 ≤ c) (T : ℝ) :
    BoundedSmoothFamily (tiltedBackward c T f g) := by
  unfold tiltedBackward
  simpa only [one_mul] using (varianceTilted_family hf hLip hg hc).reparam
    (A := fun t => T-t) (C := fun _ => 1) (measurable_const.sub measurable_id) measurable_const (fun _ => by norm_num)

end ZeroTemperatureSK.Heat
end
end
end OAI
