namespace OAI

noncomputable section

open scoped BigOperators

namespace TotientAsymptotic

theorem prefixLinear_coordinate (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    u i = ∑ j : Fin N,
      if i ≤ j then g (j.val-i.val)*prefixLinear N u j else 0 := by
  have hh := prefix_coordinate_full_sum N (extendPrefix N u) i.isLt
  have hv : extendPrefix N u (i.val+1) = u i := by simp [extendPrefix]
  rw [hv] at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← prefixLinear_vector, prefixVector_extend]
  rfl

end TotientAsymptotic
end
end OAI
