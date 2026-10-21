namespace OAI

section

noncomputable section

open MeasureTheory Set Filter Metric

open scoped NNReal ENNReal Topology

noncomputable section

open Set Filter Metric

open scoped Topology NNReal

noncomputable section

open Set Filter Metric

open scoped Topology NNReal

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

open scoped ENNReal NNReal Topology

noncomputable section

open Set

noncomputable section

open Set Filter Metric

open scoped Topology NNReal

open scoped ContDiff Manifold

noncomputable section

namespace SLEExactGauge

namespace Parameter

theorem normalized_angularDerivative_bound (P : Parameter) {δ s c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1) (hc : |c| ≤ 1) :
    |P.angularDerivative δ s c| / P.f δ s ≤
      (P.p + P.q) * (3 : ℝ) ^ P.η * δ ^ (-1 - P.η) * (P.D δ s) ^ P.η := by
  have hf := P.f_pos hδ hs
  have hfδ := P.f_ge_δ hδ.le hs.le
  have hf3 := P.f_le_three hδ.le hδ1 hs.le hs1
  have hθ := P.angularDerivative_bound hδ.le hδ1 hs hs1 hc
  have hbase : |P.angularDerivative δ s c| / P.f δ s ≤
      (P.p + P.q) / δ * s ^ (P.q - 1) := by
    calc
      _ ≤ ((P.p + P.q) * s ^ (P.q - 1)) / P.f δ s :=
        div_le_div_of_nonneg_right hθ hf.le
      _ ≤ ((P.p + P.q) * s ^ (P.q - 1)) / δ :=
        div_le_div_of_nonneg_left (by have := P.p_pos; have := P.q_pos; positivity)
          hδ hfδ
      _ = (P.p + P.q) / δ * s ^ (P.q - 1) := by ring
  have hD : (P.D δ s) ^ P.η =
      δ ^ P.η / (P.f δ s) ^ P.η * s ^ (P.q - 1) := by
    unfold D
    rw [Real.mul_rpow (div_pos hδ hf).le (Real.rpow_nonneg hs.le _),
      Real.div_rpow hδ.le hf.le, ← Real.rpow_mul hs.le, P.η_exponent]
  have hδpow : δ ^ (-1 - P.η) * δ ^ P.η = δ⁻¹ := by
    rw [← Real.rpow_add hδ]
    convert Real.rpow_neg_one δ using 1
    congr 1
    ring
  have hfη : (P.f δ s) ^ P.η ≤ (3 : ℝ) ^ P.η :=
    Real.rpow_le_rpow hf.le hf3 P.η_pos.le
  have hratio : 1 ≤ (3 : ℝ) ^ P.η / (P.f δ s) ^ P.η :=
    (one_le_div (Real.rpow_pos_of_pos hf _)).2 hfη
  rw [hD]
  have hrew : (P.p + P.q) * (3 : ℝ) ^ P.η * δ ^ (-1 - P.η) *
      (δ ^ P.η / (P.f δ s) ^ P.η * s ^ (P.q - 1)) =
      ((P.p + P.q) / δ * s ^ (P.q - 1)) *
        ((3 : ℝ) ^ P.η / (P.f δ s) ^ P.η) := by
    calc
      _ = (P.p + P.q) * s ^ (P.q - 1) * ((3 : ℝ) ^ P.η /
        (P.f δ s) ^ P.η) * (δ ^ (-1 - P.η) * δ ^ P.η) := by ring
      _ = _ := by rw [hδpow]; ring
  rw [hrew]
  exact hbase.trans (le_mul_of_one_le_right
    (by have := P.p_pos; have := P.q_pos; positivity) hratio)

end Parameter
end SLEExactGauge
end
end
end
end
end
end
end
end
end OAI
