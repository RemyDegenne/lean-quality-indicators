namespace OAI

namespace PolynomialVacuumAlgebra

theorem cup_slide_entry_5_0 (x : ℂ) :
    cupSlideLeft x .zero .plus .minus .zero = cupSlideRight x .zero .plus .minus .zero := by
  norm_num [cupSlideLeft,cupSlideRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    exchangeDenominator,cup,charge,zpow_neg,q_five_inv,T,t]
  all_goals ring_nf
  all_goals try simp only [q_pow_9,q_pow_11,q_pow_13,q_pow_15,q_pow_17,q_pow_19,q_pow_21,q_pow_23,q_pow_25,q_pow_27,q_pow_31,q_pow_33,q_pow_37]
  all_goals ring

end PolynomialVacuumAlgebra
end OAI
