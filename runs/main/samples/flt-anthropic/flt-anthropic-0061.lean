namespace P2MW.S_ModularCurve_qTwist_neg_one_lambdaModC_mul

attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve Polynomial

namespace LambdaE2Sol

section Supp

variable {R : Type*} [CommRing R]

namespace SuppGE

variable {n a b : ℤ} {x y : LaurentSeries R}

theorem qExpand' (hx : SuppGE a x) (N : ℕ) [NeZero N] : SuppGE (N * a) (ModularCurve.qExpand R N x) := by
  intro k hk
  by_cases hd : (N : ℤ) ∣ k
  · obtain ⟨k', rfl⟩ := hd
    rw [qExpand_coeff_mul]
    refine hx k' ?_
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact lt_of_mul_lt_mul_left hk hN.le
  · exact qExpand_coeff_of_not_dvd N x hd

end SuppGE
end Supp
end LambdaE2Sol
end
end P2MW.S_ModularCurve_qTwist_neg_one_lambdaModC_mul
