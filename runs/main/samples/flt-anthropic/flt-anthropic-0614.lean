namespace P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace ModularCurve

namespace PoincareDualIntegrality

p2m_open

open UpperHalfPlane Filter Complex MeasureTheory Asymptotics

open scoped MatrixGroups Topology ModularForm Real Pointwise

section Cocycle

variable {Γ : Subgroup SL(2, ℤ)} [hn : Fact ((-1 : SL(2, ℤ)) ∈ Γ)]

local notation "Q" => SL(2, ℤ) ⧸ Γ

theorem toPerm_pow_apply (M : SL(2, ℤ)) (j : ℕ) (q : Q) :
    ((MulAction.toPerm M : Equiv.Perm Q) ^ j) q = M ^ j • q := by
  induction j generalizing q with
  | zero => simp
  | succ j ih => rw [pow_succ, Equiv.Perm.mul_apply, MulAction.toPerm_apply, ih, ← mul_smul, ← pow_succ]

end Cocycle
end PoincareDualIntegrality
end ModularCurve
end
end P2MW.S_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
