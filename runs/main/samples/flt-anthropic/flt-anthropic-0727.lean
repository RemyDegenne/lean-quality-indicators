namespace P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic

set_option autoImplicit false

open MeasureTheory

namespace PMDND

variable {r c : ℕ}

lemma norm_iteratedFDeriv_dir_le {V : (Fin r → ℝ) × (Fin c → ℝ) → ℂ} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (w : (Fin r → ℝ) × (Fin c → ℝ)) (j : ℕ) (p : (Fin r → ℝ) × (Fin c → ℝ)) :
    ‖iteratedFDeriv ℝ j (dir w V) p‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (j + 1) V p‖ := by
  set L : (((Fin r → ℝ) × (Fin c → ℝ)) →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ w with hL
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ V y) := (contDiff_infty_iff_fderiv.1 hV).2
  have : dir w V = L ∘ (fun y => fderiv ℝ V y) := by funext y; simp [hL, dir]
  rw [this, ContinuousLinearMap.iteratedFDeriv_comp_left L hfd.contDiffAt (by exact_mod_cast le_top),
    ← norm_iteratedFDeriv_fderiv]
  calc ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ j (fderiv ℝ V) p)‖
      ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) p‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ V) p‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w) (fun f => ?_)
        rw [hL, ContinuousLinearMap.apply_apply, mul_comm]
        exact f.le_opNorm w

end PMDND
end P2MW.S_MeasureTheory_exists_forall_contDiff_norm_iteratedFDeriv_setIntegral_mul_cexp_le_mul_prod_of_contDiff_of_periodic
