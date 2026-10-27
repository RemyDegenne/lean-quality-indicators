namespace P2MW.S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

namespace P2MKcIgusaGroup

variable {M : ℕ} [NeZero M]

section Main

variable (H : Subgroup (AddAut (ZMod M × ZMod M)))

variable {H}

namespace Frame

variable (Fr : Frame H)

def kk : ℕ := (-(Fr.z⁻¹) : ZMod M).val

end Frame
end Main
end P2MKcIgusaGroup
end P2MW.S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem
