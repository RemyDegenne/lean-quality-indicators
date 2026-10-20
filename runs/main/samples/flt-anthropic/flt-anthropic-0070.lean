namespace P2MW.S_ModularCurve_exists_chordSlope_nonToricPoint

set_option autoImplicit false

noncomputable section

open ModularCurve

namespace SlotSeriesTransport

section Bounded

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem isBdd_slotSubst_tateUnivX (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (hc : ‖(c : K)‖ ≤ 1) (hc' : ‖((c⁻¹ : Kˣ) : K)‖ ≤ 1) :
    IsBdd (slotSubst K p c j tateUnivX) := by
  intro n
  rw [coeff_slotSubst_tateUnivX p c j hj hjp n]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · split_ifs
    · exact (norm_mul_le _ _).trans (mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _)
        (norm_nonneg _) (norm_units_pow_le hc _))
    · simp
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun M _ => ?_
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun e _ => ?_
    refine (norm_mul_le _ _).trans (mul_le_one₀ (IsUltrametricDist.norm_natCast_le_one K _)
      (norm_nonneg _) ?_)
    have h2 : ‖(if n = p * M then (2 : K) else 0)‖ ≤ 1 := by
      split_ifs
      · exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2
      · simp
    have hA : ‖(if n = p * M + j * e then (c : K) ^ e else 0)‖ ≤ 1 := by
      split_ifs
      · exact norm_units_pow_le hc e
      · simp
    have hB : ‖(if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0)‖ ≤ 1 := by
      split_ifs
      · exact norm_units_pow_le hc' e
      · simp
    exact (norm_sub_le_max' _ _).trans
      (max_le ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA hB)) h2)

end Bounded
end SlotSeriesTransport
end
end P2MW.S_ModularCurve_exists_chordSlope_nonToricPoint
