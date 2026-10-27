namespace P2MW.S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC

set_option linter.unusedSectionVars false

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups

p2m_open

namespace ModularCurve

namespace GaussQExpRP

p2m_open

section Gauss

variable {Γ : Subgroup SL(2, ℤ)}

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)

variable (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

local notation "kk" => IsLocalRing.ResidueField A

def gaussRing : ValuationSubring FF where
  carrier := {f | IsInt A (f : LaurentSeries L)}
  mul_mem' {f g} hf hg := by
    change IsInt A ((f * g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_mul]; exact hf.mul hg
  one_mem' := by change IsInt A ((1 : FF) : LaurentSeries L); exact IsInt.one
  add_mem' {f g} hf hg := by
    change IsInt A ((f + g : FF) : LaurentSeries L)
    rw [IntermediateField.coe_add]; exact hf.add hg
  zero_mem' := by change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
  neg_mem' {f} hf := by
    change IsInt A ((-f : FF) : LaurentSeries L)
    rw [IntermediateField.coe_neg]; exact hf.neg
  mem_or_inv_mem' f := by
    by_cases hf : f = 0
    · left; subst hf; change IsInt A ((0 : FF) : LaurentSeries L); exact IsInt.zero
    obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h, -⟩ := exists_frac_form A hT f hf
    rcases A.mem_or_inv_mem c with hc | hc
    · left
      refine ⟨HahnSeries.C ⟨c, hc⟩ * x₀, y₀, hy₀, ?_⟩
      rw [h, map_mul, ι_C]
    · right
      change IsInt A ((f⁻¹ : FF) : LaurentSeries L)
      refine ⟨HahnSeries.C ⟨c⁻¹, hc⟩ * y₀, x₀, hx₀, ?_⟩
      have hf' : (f : LaurentSeries L) ≠ 0 := fun h' => hf (Subtype.ext h')
      rw [IntermediateField.coe_inv, map_mul, ι_C]
      have hcC : algebraMap L (LaurentSeries L) c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      calc (f : LaurentSeries L)⁻¹ * ι A x₀
          = (f : LaurentSeries L)⁻¹ * (algebraMap L (LaurentSeries L) c)⁻¹ *
              ((f : LaurentSeries L) * ι A y₀) := by rw [h]; field_simp
        _ = algebraMap L (LaurentSeries L) (↑(⟨c⁻¹, hc⟩ : A) : L) * ι A y₀ := by
              rw [map_inv₀]; field_simp

end Gauss
end GaussQExpRP
end ModularCurve
end
end P2MW.S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
