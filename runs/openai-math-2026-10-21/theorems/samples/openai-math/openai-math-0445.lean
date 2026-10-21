namespace OAI

namespace BFSS

noncomputable section

lemma massive_potential_scaling {N : ℕ} (h m : ℝ) (hh : 0 < h) (hm : 0 < m)
    (x : Configuration N) :
    massivePotential h m x = (m ^ 4 / h ^ 2) *
      massivePotential 1 1 (scaleConfiguration (h / m) x) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hres (a b c : Mat N) :
      realBracket ((h / m) • a) ((h / m) • b) - (2 : ℝ) • ((h / m) • c) =
      (h / m ^ 2) • ((h : ℂ) • realBracket a b - (2 * m : ℝ) • c) := by
    rw [realBracket_real_smul, smul_sub, smul_smul]
    congr 1
    · ext i j
      simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_div,
        Complex.ofReal_pow]
      field_simp
    · rw [smul_smul]
      congr 1
      field_simp
  dsimp only [massivePotential, scaleConfiguration]
  unfold Configuration Color at x
  simp only [one_pow, one_mul, mul_one, Complex.ofReal_one, one_smul]
  rw [hres, hres, hres]
  simp only [realBracket_real_smul, hsNormSq_real_smul]
  have hsum : (∑ i : Fin 9, ∑ j : Fin 9,
      if i < j ∧ 3 ≤ j.val then ((h / m) ^ 2) ^ 2 * hsNormSq
        (realBracket (x i).val (x j).val) else 0) =
      ((h / m) ^ 2) ^ 2 * (∑ i : Fin 9, ∑ j : Fin 9,
      if i < j ∧ 3 ≤ j.val then hsNormSq
        (realBracket (x i).val (x j).val) else 0) := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  have hsum2 : (∑ i : Fin 9,
      if 3 ≤ i.val then (h / m) ^ 2 * hsNormSq (x i).val else 0) =
      (h / m) ^ 2 * (∑ i : Fin 9, if 3 ≤ i.val then hsNormSq (x i).val else 0) := by
    simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [hsum, hsum2]
  field_simp

end
end BFSS
end OAI
