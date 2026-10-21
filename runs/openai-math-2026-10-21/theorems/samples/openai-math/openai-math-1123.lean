namespace OAI

section

open Set MeasureTheory Filter

open scoped InnerProductSpace Topology NNReal

open Set Filter

open scoped Topology NNReal

open Set MeasureTheory Filter

open scoped Topology NNReal ENNReal

open scoped ENNReal

open scoped InnerProductSpace ContDiff Topology

open scoped ENNReal

open Set MeasureTheory Filter

open scoped ENNReal Topology

noncomputable section

namespace QuadraticRegularity

open Filter

open scoped Topology InnerProductSpace NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hasFDerivAt_of_remainder {φ : E → ℝ} {P : E → E} {C : ℝ}
    (hc : ∀ x y, |φ y-φ x-⟪P x,y-x⟫_ℝ| ≤ C*‖y-x‖^2) (x : E) :
    HasFDerivAt φ (innerSL ℝ (P x)) x := by
  rw [hasFDerivAt_iff_isLittleO]
  have hh : (fun y => φ y-φ x-(innerSL ℝ (P x)) (y-x)) =O[𝓝 x]
      (fun y => ‖y-x‖^2) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C,Filter.Eventually.of_forall fun y => ?_⟩
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖y-x‖),innerSL_apply_apply] using hc x y
  exact hh.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < (2:ℕ)))

end QuadraticRegularity
end
end
end OAI
