namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct Quaternion NumberField Pointwise

open IsDedekindDomain NumberField

noncomputable section

namespace K3cSplit

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

section Quaternion

variable {a b : ℚ}

theorem nrd_ne_zero_of_ne_zero (ha : a < 0) (hb : b < 0) {h : ℍ[ℚ, a, b]} (h0 : h ≠ 0) :
    QuaternionAlgebra.nrd h ≠ 0 := by
  intro hn
  apply h0
  obtain ⟨h₀, h₁, h₂, h₃⟩ := h
  simp only [QuaternionAlgebra.nrd_mk] at hn
  have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
  have s0 := sq_nonneg h₀
  have s1 : 0 ≤ -a * h₁ ^ 2 := mul_nonneg (by linarith) (sq_nonneg h₁)
  have s2 : 0 ≤ -b * h₂ ^ 2 := mul_nonneg (by linarith) (sq_nonneg h₂)
  have s3 : 0 ≤ a * b * h₃ ^ 2 := mul_nonneg hab.le (sq_nonneg h₃)
  have e0 : h₀ ^ 2 = 0 := by linarith
  have e1 : -a * h₁ ^ 2 = 0 := by linarith
  have e2 : -b * h₂ ^ 2 = 0 := by linarith
  have e3 : a * b * h₃ ^ 2 = 0 := by linarith
  have f0 : h₀ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e0
  have f1 : h₁ = 0 := by
    rcases mul_eq_zero.mp e1 with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have f2 : h₂ = 0 := by
    rcases mul_eq_zero.mp e2 with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have f3 : h₃ = 0 := by
    rcases mul_eq_zero.mp e3 with h | h
    · linarith
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  subst f0; subst f1; subst f2; subst f3
  rfl

end Quaternion
end K3cSplit
end
end P2MW.S_QuaternionAlgebra_IsMaximalOrder_exists_ofFiniteIdele_eq_inf_setOf_le_padicValRat_nrd
