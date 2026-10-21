namespace OAI

namespace JointDickman

open Finset

lemma squarefree_logarithmic_bilinear_error (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    (hsupport : ∀ n, ¬Squarefree n → f n = 0) (N : ℕ) (θ : ℝ) :
    ‖(∑ n ∈ Ioc 0 N, ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ)) -
      primeLogBilinear f N θ‖ ≤ primeSquareLogError N := by
  rw [←prime_log_bilinear_identity,←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  have he : ((f n*Real.log n:ℝ):ℂ)*additivePhase ((n:ℝ)*θ) -
      (∑ p ∈ n.primeFactors, ((f p*f (n/p)*Real.log p:ℝ):ℂ)*additivePhase ((n:ℝ)*θ)) =
      ((f n*Real.log n - ∑ p ∈ n.primeFactors, f p*f (n/p)*Real.log p:ℝ):ℂ)*
        additivePhase ((n:ℝ)*θ) := by
    simp only [Complex.ofReal_sub,Complex.ofReal_sum,sub_mul,sum_mul]
  rw [he,norm_mul,norm_additivePhase,mul_one,Complex.norm_real,Real.norm_eq_abs]
  exact squarefree_supported_log_error f hf hb hsupport n

end JointDickman
end OAI
