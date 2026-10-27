public section

namespace CFSG.Semidihedral.UnitaryDValue

section General

variable {G : Type*} [Group G]

theorem zpow_pow_comm' (a : G) (j : ℤ) (k : ℕ) : (a ^ j) ^ k = (a ^ k) ^ j := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm j, zpow_mul, zpow_natCast]

end General
end CFSG.Semidihedral.UnitaryDValue
end
