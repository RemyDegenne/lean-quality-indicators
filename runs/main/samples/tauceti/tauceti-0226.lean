public section

noncomputable section

open MeasureTheory Set

open scoped ENNReal unitInterval

namespace TauCeti

namespace unitInterval

variable {m i : ℕ}

theorem volume_preimage_cellIdx (hi : i < m) :
    volume (cellIdx m ⁻¹' {i}) = (m : ℝ≥0∞)⁻¹ := by
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.zero_le i) hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hα : (i : ℝ) / m ∈ I :=
    ⟨by positivity, (div_le_one hmR).2 (by exact_mod_cast hi.le)⟩
  -- the two cases contribute the same value, computed from different intervals
  have hgoal : volume (cellIdx m ⁻¹' {i}) = ENNReal.ofReal (1 / (m : ℝ)) := by
    rcases (Nat.succ_le_of_lt hi).lt_or_eq with hlt | heq
    · -- below the top: the fibre is `[i/m, (i+1)/m)`
      have hβ : ((i : ℝ) + 1) / m ∈ I :=
        ⟨by positivity, (div_le_one hmR).2 (by exact_mod_cast hlt.le)⟩
      have hset : cellIdx m ⁻¹' {i} = Ico (⟨(i : ℝ) / m, hα⟩ : I) ⟨((i : ℝ) + 1) / m, hβ⟩ := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_Ico, ← Subtype.coe_le_coe,
          ← Subtype.coe_lt_coe]
        exact cellIdx_eq_iff_of_succ_lt hlt x
      rw [hset, _root_.unitInterval.volume_Ico]
      congr 1
      field_simp
      ring
    · -- the top cell: the fibre is `[(m-1)/m, 1]`
      have hset : cellIdx m ⁻¹' {i} = Ici (⟨(i : ℝ) / m, hα⟩ : I) := by
        ext x
        simp only [mem_preimage, mem_singleton_iff, mem_Ici, ← Subtype.coe_le_coe]
        have hi_top : i = m - 1 := by omega
        simpa [hi_top] using cellIdx_eq_sub_one_iff hm0 x
      rw [hset, _root_.unitInterval.volume_Ici]
      congr 1
      have : (i : ℝ) + 1 = m := by exact_mod_cast heq
      field_simp
      linarith
  rw [hgoal, one_div, ENNReal.ofReal_inv_of_pos hmR, ENNReal.ofReal_natCast]

end unitInterval
end TauCeti
end
end
