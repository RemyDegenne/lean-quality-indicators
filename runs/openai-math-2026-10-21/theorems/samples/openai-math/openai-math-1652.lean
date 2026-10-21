namespace OAI

namespace PolynomialVacuumAlgebra

theorem yb_entry_8_9 (x y : ℂ) :
    ybLeft x y .zero .minus .minus .plus .zero .zero = ybRight x y .zero .minus .minus .plus .zero .zero := by
  simp only [ybLeft,ybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

end PolynomialVacuumAlgebra
end OAI
