public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringU38M

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial Matrix

open CFSG.GH74.GLS.IVK (fixedField)

open CFSG.GH74.KGroups

section Regular

variable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)

theorem eigen_eta {B y : Matrix (Fin 3) (Fin 3) K} {c : K} (hB : adjM h B * B = 1)
    (hB3 : B * B * B = c • (1 : Matrix (Fin 3) (Fin 3) K)) {l : K} (hl9 : l ^ 9 = 1)
    (hl3 : l ^ 3 = c) {v : Fin 3 → K} (hv : v ≠ 0) (hBv : B *ᵥ v = l • v) {a b d : K}
    (hyp : y = a • (1 : Matrix (Fin 3) (Fin 3) K) + b • B + d • (B * B))
    (hy : adjM h y * y = 1) (hy7 : y ^ 7 = 1) : a + b * l + d * l ^ 2 = 1 := by
  haveI := h.charP
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl9
  have hc0 : c ≠ 0 := by
    rw [← hl3]
    exact pow_ne_zero _ hl0
  set η : K := a + b * l + d * l ^ 2 with hη
  have hyv : y *ᵥ v = η • v := by
    rw [hyp]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hBv, Matrix.mulVec_smul, smul_smul, hη]
    module
  have hypow : ∀ n : ℕ, (y ^ n) *ᵥ v = η ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hyv, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm]
  have hη7 : η ^ 7 = 1 := by
    have h1 := hypow 7
    rw [hy7, Matrix.one_mulVec] at h1
    have h2 : (η ^ 7 - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv
  have hBBadj : B * B = c • adjM h B := by
    have h1 : adjM h B * (B * B * B) = c • adjM h B := by
      rw [hB3, Matrix.mul_smul, Matrix.mul_one]
    have h2 : adjM h B * (B * B * B) = B * B := by
      calc adjM h B * (B * B * B) = (adjM h B * B) * B * B := by simp only [Matrix.mul_assoc]
        _ = B * B := by rw [hB, Matrix.one_mul]
    rw [← h2, h1]
  have hbar : h.bar l * c = l ^ 2 := by
    rw [h.bar_apply, ← hl3]
    have : l ^ 11 = l ^ 2 := by
      calc l ^ 11 = l ^ 9 * l ^ 2 := by ring
        _ = l ^ 2 := by rw [hl9, one_mul]
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← this]
    ring
  have hadjBv : adjM h B *ᵥ v = h.bar l • v := by
    have h1 : (B * B) *ᵥ v = (l ^ 2) • v := by
      rw [← Matrix.mulVec_mulVec, hBv, Matrix.mulVec_smul, hBv, smul_smul, pow_two]
    have h2 : c • (adjM h B *ᵥ v) = (l ^ 2) • v := by
      rw [← Matrix.smul_mulVec, ← hBBadj, h1]
    have h3 : c • (adjM h B *ᵥ v) = c • (h.bar l • v) := by
      rw [h2, smul_smul, mul_comm, hbar]
    exact smul_right_injective _ hc0 h3
  have hadjy : adjM h y = h.bar a • (1 : Matrix (Fin 3) (Fin 3) K) + h.bar b • adjM h B +
      h.bar d • (adjM h B * adjM h B) := by
    rw [hyp, adjM_add, adjM_add, adjM_smul, adjM_smul, adjM_smul, adjM_one, adjM_mul]
  have hadjyv : adjM h y *ᵥ v = h.bar η • v := by
    rw [hadjy]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hadjBv, Matrix.mulVec_smul, smul_smul, hη, map_add, map_mul, map_pow]
    module
  have hN : η * h.bar η = 1 := by
    have h1 : v = (adjM h y * y) *ᵥ v := by rw [hy, Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, hyv, Matrix.mulVec_smul, hadjyv, smul_smul] at h1
    have h2 : (η * h.bar η - 1) • v = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 hv
  have hη9 : η ^ 9 = 1 := by
    rw [h.bar_apply] at hN
    rw [← hN, show (2 : ℕ) ^ 3 = 8 by norm_num]
    ring
  have hη2 : η ^ 2 = 1 := by
    calc η ^ 2 = η ^ 2 * η ^ 7 := by rw [hη7, mul_one]
      _ = η ^ 9 := by ring
      _ = 1 := hη9
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  have h4 : (η - 1) ^ 2 = 0 := by linear_combination hη2 + (1 - η) * h2K
  have h5 := pow_eq_zero_iff (two_ne_zero) |>.mp h4
  exact sub_eq_zero.mp h5

end Regular
end CFSG.RankThree.PartTwo.Sec8.HeringU38M
end
