namespace OAI

namespace PolynomialVacuumAlgebra

theorem yb_entry_12_18 (x y : ℂ) :
    ybLeft x y .plus .plus .zero .minus .zero .zero = ybRight x y .plus .plus .zero .minus .zero .zero := by
  simp only [ybLeft,ybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,add_zero]

end PolynomialVacuumAlgebra
end OAI
