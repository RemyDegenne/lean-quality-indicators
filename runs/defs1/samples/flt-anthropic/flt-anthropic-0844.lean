namespace P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow

attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

open scoped TensorProduct

open Function

universe u v

namespace HopfAlgebra

namespace CocycleSplit

p2m_open

section SqZero

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R]

variable (ε : R →ₐ[k] k) (c : R →ₗ[k] R →ₗ[k] k)

def Sq (_ε : R →ₐ[k] k) (_c : R →ₗ[k] R →ₗ[k] k) : Type (max u v) := R × k

end SqZero
end CocycleSplit
end HopfAlgebra
end
end P2MW.S_HopfAlgebra_exists_forall_apply_mul_eq_of_symm_cocycle_of_forall_apply_pow_pred_eq_pow
