namespace OAI

noncomputable section

namespace ScalarConductivity

open Set MeasureTheory Filter Topology UnitAddTorus

open scoped NNReal ENNReal

lemma faceRayDensityLower_pos {w : ℝ} (hw : 0<w) : 0<faceRayDensityLower w := by
  unfold faceRayDensityLower
  positivity

end ScalarConductivity
end
end OAI
