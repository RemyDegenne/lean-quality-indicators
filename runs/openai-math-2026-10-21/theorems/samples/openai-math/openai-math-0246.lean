namespace OAI

namespace PolynomialVacuumAlgebra

theorem hyb_entry_13_21 (x y z : ℂ) :
    hybLeft x y z .plus .plus .plus .minus .plus .zero = hybRight x y z .plus .plus .plus .minus .plus .zero := by
  simp only [hybLeft,hybRight,sum_spin,exchangeNumerator_eq_table,exchangeTable,
    mul_zero,zero_mul,zero_add,add_zero]

end PolynomialVacuumAlgebra
end OAI
