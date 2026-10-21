namespace OAI

namespace PolynomialVacuumAlgebra

theorem yb_entry_1_1 (x y : ℂ) :
    ybLeft x y .zero .zero .plus .zero .zero .plus = ybRight x y .zero .zero .plus .zero .zero .plus := by
  simp only [ybLeft,ybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]
  all_goals ring_nf
  all_goals try simp only [q_pow_eight,q_pow_10,q_pow_12,q_pow_14,q_pow_16,q_pow_18]
  all_goals ring

end PolynomialVacuumAlgebra
end OAI
