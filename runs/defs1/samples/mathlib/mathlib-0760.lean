@[expose] public section

open Function (Injective Surjective)

variable {M N G H α β γ δ : Type*}

export SemigroupAction (mul_smul)

export AddSemigroupAction (add_vadd)

export SMulCommClass (smul_comm)

export VAddCommClass (vadd_comm)

export SMulDistribClass (smul_distrib_smul)

export IsCentralVAdd (op_vadd_eq_vadd unop_vadd_eq_vadd)

export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

export MulDistribMulAction (smul_one)

export AddDistribAddAction (vadd_zero)

section IsCancelSMul

variable (G P : Type*)

/-- A scalar multiplication is left-cancellative if it is pointwise injective on the left. -/
@[to_additive]
class IsLeftCancelSMul [SMul G P] : Prop where
  protected left_cancel' : ∀ (a : G) (b c : P), a • b = a • c → b = c

end IsCancelSMul
end
