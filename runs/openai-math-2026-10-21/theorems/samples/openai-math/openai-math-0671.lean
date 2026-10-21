namespace OAI

namespace PlanarFalconer

open Set MeasureTheory

open scoped ENNReal NNReal

theorem radialEnergyMajorant_lt_top (α β : Measure Plane) {D s t p : ℝ}
    (hp : 0 < p) (hp2 : p < 2) (ht : 0 < t) (htp : t < 2-p)
    (hα : rieszEnergy α s < ∞) (hβ : rieszEnergy β t < ∞) :
    radialEnergyMajorant α β D s t p < ∞ := by
  unfold radialEnergyMajorant
  apply ENNReal.mul_lt_top
  · exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  · apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by linarith)
          (angularEnergyConstant_lt_top (div_pos ht (sub_pos.mpr hp2))
            ((div_lt_one (sub_pos.mpr hp2)).mpr htp)).ne)
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hβ.ne)
    · exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
        (ENNReal.mul_lt_top (by norm_num) hα).ne

end PlanarFalconer
end OAI
