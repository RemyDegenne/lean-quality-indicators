namespace OAI

noncomputable section

open scoped BigOperators

open Finset

open Finset Classical

open Filter

open Finset Classical Filter

open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem

open OrdinaryCorrelations.SignedTrace

open Finset Classical Filter

lemma source_witness_delta_saving (C₀ : ℝ) (h : ℕ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      sourceWitnessDelta C₀ h B ≤ Real.exp (-(1/2)*B^(1-epsilon)) := by
  let C := (C₀+4*(h:ℝ)+3)/Real.log 2+3
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 ≤ C₀+4*(h:ℝ)+3 := by positivity
  filter_upwards [eventually_const_pow_le_exp_rpow C (1-epsilon) (1/2) 2
    (by norm_num [epsilon]) (by norm_num),eventually_ge_atTop (1:ℝ)] with B hp hB
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hP : 0 < sourceMinPrime B := Real.exp_pos _
  have hb2 : B ≤ B^2 := by nlinarith
  have hK := source_testSize_polynomial h C₀ B hC₀ hB
  have hmax : sourceWitnessDelta C₀ h B ≤ C*B^2/sourceMinPrime B := by
    unfold sourceWitnessDelta
    apply max_le
    · rw [div_mul_eq_div_div_swap]
      apply div_le_div_of_nonneg_right _ hP.le
      apply (div_le_div_of_nonneg_right hK hlog.le).trans
      dsimp only [C]
      rw [mul_div_right_comm]
      nlinarith [sq_nonneg B]
    · apply div_le_div_of_nonneg_right _ hP.le
      have := div_nonneg hC hlog.le
      dsimp only [C]
      nlinarith
  apply hmax.trans
  calc
    C*B^2/sourceMinPrime B ≤ Real.exp ((1/2)*B^(1-epsilon))/Real.exp (B^(1-epsilon)) :=
      div_le_div_of_nonneg_right hp hP.le
    _ = _ := by rw [←Real.exp_sub]; congr 1; ring

end OrdinaryCorrelations.GraphKernel.PrimeSystem
end
end OAI
