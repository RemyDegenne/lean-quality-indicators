@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

open scoped commutatorElement

theorem tauhat_sq_conj_xhat : tauhat ^ 2 * xhat * (tauhat ^ 2)⁻¹ = yhat := by
  rw [tauhat, ← iotaD_xbar, yhat, ← map_pow, ← map_inv, ← map_mul, ← map_mul,
    ← conj_conj_eq_sq, taubar_conj_xbar, taubar_conj_ybar]

end CFSG.Monster.B.TwoA
end
