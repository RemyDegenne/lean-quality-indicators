namespace OAI

noncomputable section

namespace CubicFirstMoment

lemma smallPartModulus_norm_le {v a b q : Eisenstein}
    (hsa : Squarefree a) (hsb : Squarefree b) (hv : v ≠ 0) :
    norm ((3*(primarySmallPart v a*primarySmallPart v b))*q) ≤ 9*norm v^2*norm q := by
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  rw [norm_mul_eq,norm_mul_eq,norm_mul_eq,h3]
  have ha := norm_le_of_dvd hv (primarySmallPart_dvd hsa hv)
  have hb := norm_le_of_dvd hv (primarySmallPart_dvd hsb hv)
  have hmul := mul_le_mul ha hb (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by norm_num : (0:ℝ) ≤ 9)) (norm_nonneg q)]

end CubicFirstMoment
end
end OAI
