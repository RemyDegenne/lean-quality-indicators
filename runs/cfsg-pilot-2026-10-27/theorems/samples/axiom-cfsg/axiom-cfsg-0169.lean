public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank

open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small

open CFSG.ClassicalInvolution.ModelFacts

open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel

open CFSG.ComponentClassification.CatalogueBOrthogonalSmallFamilyOrbit

open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open scoped MatrixGroups Pointwise

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_of_det_eq_zero (hK : Nat.card K = 3) {m : Matrix (Fin 2) (Fin 2) K}
    (h1 : m.det = 0)
    (h2 : ((weylS : SL(2, K)) * m + m * (weylS : SL(2, K))).det = 0) : m = 0 := by
  have hsq : ∀ a b : K, a * a + b * b = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    by_cases ha : a = 0
    · rw [ha, zero_mul, zero_add, mul_self_eq_zero] at hab
      exact ⟨ha, hab⟩
    · exfalso
      apply mul_self_ne_neg_one_of_card_three hK (b / a)
      field_simp
      linear_combination hab
  have hdet : ((weylS : SL(2, K)) * m + m * (weylS : SL(2, K))).det =
      (m 0 1 - m 1 0) * (m 0 1 - m 1 0) + (m 0 0 + m 1 1) * (m 0 0 + m 1 1) := by
    simp only [weylS, Matrix.det_fin_two, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [hdet] at h2
  obtain ⟨h3, h4⟩ := hsq _ _ h2
  rw [Matrix.det_fin_two] at h1
  have h5 : m 0 0 * m 0 0 + m 0 1 * m 0 1 = 0 := by
    linear_combination -h1 + (m 0 0) * h4 + (m 0 1) * h3
  obtain ⟨h6, h7⟩ := hsq _ _ h5
  have h8 : m 1 0 = 0 := by linear_combination -h3 + h7
  have h9 : m 1 1 = 0 := by linear_combination h4 - h6
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h6, h7, h8, h9]

end CFSG.ClassicalInvolution.Q3.Q3T
end
