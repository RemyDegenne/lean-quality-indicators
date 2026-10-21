namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric

open scoped Topology NNReal

namespace CoulombAnalysis

lemma field_upper_from_good_gap {W D H eta C : ℝ}
    (hD : 0 ≤ D) (hH : 0 ≤ H) (heta : 0 < eta) (hC : 0 ≤ C)
    (hg : D ≤ eta → W ≤ H) (hc : W ≤ C) :
    W ≤ H+(C/eta)*D := by
  by_cases hd : D ≤ eta
  · have hh := hg hd
    have hb : 0 ≤ (C/eta)*D := mul_nonneg (div_nonneg hC heta.le) hD
    linarith
  · have hb : C ≤ (C/eta)*D := by
      calc
        C = (C/eta)*eta := (div_mul_cancel₀ C heta.ne').symm
        _ ≤ (C/eta)*D := mul_le_mul_of_nonneg_left (le_of_not_ge hd) (div_nonneg hC heta.le)
    linarith

end CoulombAnalysis
end
end OAI
