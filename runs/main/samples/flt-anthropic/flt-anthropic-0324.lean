namespace P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

open NumberField.AdelicHaar

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

open scoped ModularForm

noncomputable section

namespace Ws41

namespace Lift7

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane AutomorphicForm.SiegelCoordinates HeckeIntegralSeam

open scoped MatrixGroups ModularForm

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

variable {M : ℕ}

theorem slash_two_scalar (f : UpperHalfPlane → ℂ) (c : GL (Fin 2) ℝ) (r : ℝ) (hr : r ≠ 0)
    (hc : (c : Matrix (Fin 2) (Fin 2) ℝ) = r • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    f ∣[(2 : ℤ)] c = f := by
  have h00 : c 0 0 = r := by
    have := congr_fun (congr_fun hc 0) 0; simpa using this
  have h01 : c 0 1 = 0 := by
    have := congr_fun (congr_fun hc 0) 1; simpa using this
  have h10 : c 1 0 = 0 := by
    have := congr_fun (congr_fun hc 1) 0; simpa using this
  have h11 : c 1 1 = r := by
    have := congr_fun (congr_fun hc 1) 1; simpa using this
  have hdet : c.det.val = r * r := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdetpos : 0 < c.det.val := by rw [hdet]; exact mul_self_pos.mpr hr
  have hsmul : ∀ z : UpperHalfPlane, c • z = z := by
    intro z
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos, UpperHalfPlane.num, UpperHalfPlane.denom, h00, h01, h10, h11]
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    push_cast
    rw [zero_mul, zero_add, add_zero, mul_div_cancel_left₀ _ hr']
  funext z
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hdetpos, hsmul z, UpperHalfPlane.denom, h10, h11,
    hdet]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [ContinuousAlgEquiv.refl_apply, Complex.ofReal_zero, zero_mul, zero_add]
  field_simp
  rw [abs_of_nonneg (sq_nonneg r), show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one]
  push_cast
  ring

end Lift7
end Ws41
end
end P2MW.S_CuspForm_IsAdelicLiftOfGamma1_isHeckeCosetEigenfunctionAt_productionPinsGeneral_of_heckeU_add_smul_slash_heckeDiagMatrix_eq
