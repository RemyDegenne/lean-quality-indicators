namespace P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt

attribute [-instance] CerednikDrinfeld.CosetGraph.projGraphAction CerednikDrinfeld.CosetGraph.projVertMulAction CerednikDrinfeld.CosetGraph.awayVertMulAction CerednikDrinfeld.CosetGraph.actionKer_normal CerednikDrinfeld.CosetGraph.vertMulAction CerednikDrinfeld.Mumford.dartAction

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option linter.style.multiGoal false

set_option linter.unusedSimpArgs false

set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

noncomputable section

namespace ALRAMN

section Uniqueness

variable {a b : ℚ}

@[scoped simp] theorem val_unitOfNrd (s : ℍ[ℚ, a, b]) (r : ℚ) (hs : QuaternionAlgebra.nrd s = r) (hr : r ≠ 0) :
    ((unitOfNrd s r hs hr : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = s := rfl

end Uniqueness
end ALRAMN
end
end P2MW.S_QuaternionAlgebra_IsEichlerOrder_exists_nrd_eq_and_forall_exists_isUnitOf_mul_eq_of_isIndefiniteRamifiedExactlyAt
