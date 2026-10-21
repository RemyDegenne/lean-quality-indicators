namespace OAI

noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

open scoped BigOperators ComplexConjugate

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology BigOperators

open MeasureTheory ProbabilityTheory Real Complex

open scoped ENNReal ComplexConjugate

open ProbabilityTheory

namespace HardSphere.Wiener

lemma coordinate_tail8 (i : Index) {a : ℝ} (ha : 0 < a) :
    law {ω | a ≤ |ω i|} ≤ (ENNReal.ofReal a)⁻¹ ^ (8 : ℕ) * moment8 := by
  have hm := memLp_id_gaussianReal' (μ := 0) (v := 1) 8 (by norm_num)
  have he : eLpNorm (fun ω : Noise ↦ ω i) 8 law =
      eLpNorm (id : ℝ → ℝ) 8 (gaussianReal 0 1) := by
    simpa only [Function.comp_def, id_eq] using
      (eLpNorm_comp_measurePreserving (p := 8) (g := (id : ℝ → ℝ))
        hm.aestronglyMeasurable (coordinate_preserving i))
  have ht := meas_ge_le_mul_pow_eLpNorm_enorm law (p := 8) (by norm_num) (by norm_num)
    (f := fun noise : Noise ↦ noise i)
    (ε := ENNReal.ofReal a) (ne_of_gt (ENNReal.ofReal_pos.mpr ha)) (by simp)
  have hs : {ω : Noise | ENNReal.ofReal a ≤ ‖ω i‖ₑ} = {ω | a ≤ |ω i|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)
  simpa only [Function.comp_def, id_eq, ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast,
    Nat.cast_ofNat, he, hs, moment8] using ht

end HardSphere.Wiener
end
end OAI
