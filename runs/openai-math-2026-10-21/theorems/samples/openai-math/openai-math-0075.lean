namespace OAI

noncomputable section

namespace KaplanskyConsequences.Regular

open scoped ComplexOrder InnerProductSpace BigOperators ENNReal

attribute [local instance] Classical.propDecidable

variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

lemma creation_orthogonal {m n : ℕ} (h : m ≠ n) :
    star (creation (H:=H) m) * creation n = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply (ext_inner_left ℂ)
  intro y
  change inner ℂ y ((creation m).adjoint (creation n x)) = inner ℂ y 0
  rw [ContinuousLinearMap.adjoint_inner_right,inner_zero_right,lp.inner_eq_tsum]
  rw [← (tsum_zero : (∑' _ : F2, (0 : ℂ)) = 0)]
  apply tsum_congr
  intro w
  by_cases hm : Prefix (m:ℤ) true (coordinate w)
  · have hn : ¬ Prefix (n:ℤ) true (coordinate w) := by
      intro hn
      exact h (Int.ofNat_inj.mp (prefix_disjoint hm hn).1)
    rw [creation_support n x w hn,inner_zero_right]
  · rw [creation_support m y w hm,inner_zero_left]

end KaplanskyConsequences.Regular
end
end OAI
