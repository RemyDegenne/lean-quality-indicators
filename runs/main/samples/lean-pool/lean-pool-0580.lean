@[expose] public section

namespace O3

theorem one_lt_belowQ {kappa sigma : ℝ}
    (hkappa : 1 < kappa) (hsigma : 0 < sigma) (hsigma1 : sigma < 1) :
    1 < belowQ kappa sigma := by
  have hsigma_sq : sigma ^ 2 < 1 := by nlinarith [sq_nonneg sigma]
  have hsigma_four : sigma ^ 4 < 1 := by
    nlinarith [sq_nonneg (sigma ^ 2)]
  have hkappa_sq : 1 < kappa ^ 2 := by nlinarith [sq_nonneg kappa]
  have hsigma_four_pos : 0 < sigma ^ 4 := pow_pos hsigma 4
  rw [belowQ, lt_div_iff₀ hsigma_four_pos]
  nlinarith

end O3
end
