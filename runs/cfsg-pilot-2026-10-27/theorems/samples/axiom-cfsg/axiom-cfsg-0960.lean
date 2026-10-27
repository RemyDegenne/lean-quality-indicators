namespace CFSG.FeitThompson

public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open Module

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {q : ℕ}

namespace ScalarLineSystem

variable (S : ScalarLineSystem k V q)

theorem lineScalar_mul (i : ZMod q) (a a' : S.A) :
    S.lineScalar i (a * a') = S.lineScalar i a * S.lineScalar i a' := by
  refine (S.eq_lineScalar i (a * a') ?_).symm
  intro v hv
  have h1 : ((a * a' : S.A) : V ≃ₗ[k] V) v = (a : V ≃ₗ[k] V) ((a' : V ≃ₗ[k] V) v) := by
    simp [LinearEquiv.mul_apply]
  rw [h1, S.apply_eq_lineScalar_smul i a' hv, map_smul, S.apply_eq_lineScalar_smul i a hv]
  simp [smul_smul, mul_comm]

end ScalarLineSystem
end
end CFSG.FeitThompson
