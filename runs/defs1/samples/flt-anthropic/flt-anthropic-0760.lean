namespace P2MW.S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure

set_option autoImplicit false

set_option linter.unusedSectionVars false

namespace FreeCoresSol

open MulAction Subgroup

attribute [local instance] arrowAction arrowMulDistribMulAction

section General

variable {F : Type*} [Group F] {R : Subgroup F} {A : Type*} [CommGroup A]

section Finite

variable [R.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def total (f : V R A) : A := ∏ q, f q

end Finite
end General
end FreeCoresSol
end P2MW.S_IsFreeGroup_surjective_transfer_and_transfer_eq_one_iff_mem_closure
