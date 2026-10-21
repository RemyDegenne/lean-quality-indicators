namespace OAI

namespace PolynomialVacuumAlgebra

theorem baseThree_rotation_16 (x y z : ℂ) :
    zeta ^ charge .plus * baseThree x y z .minus .plus .plus =
    baseThree z x y .plus .minus .plus := by
  norm_num [baseTwo,baseThree,baseThreeFactor,sum_pair,sum_spin,
    exchangeNumerator_eq_table,exchangeTable,exchangeDenominator,cup,charge,zpow_neg,
    q_five_inv,q_four_inv,T,t,zeta,inv_pow,q_inv]

end PolynomialVacuumAlgebra
end OAI
