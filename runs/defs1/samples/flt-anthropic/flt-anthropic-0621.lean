namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSimpArgs false

set_option linter.unusedSectionVars false

noncomputable section

p2m_open

universe u

namespace AlgebraicGeometry

namespace OModulePresheaf

namespace IterCech

namespace Staircase

p2m_open

section Tuples

variable {ιP ιU ιV : Type*}

def tupKB (sndP : ιP → ιV) (n p q : ℕ) (h : p + q = n) (K : Fin (n + 1) → ιP) : Fin (q + 1) → ιV :=
  fun j => sndP (K ⟨p + j, by omega⟩)

end Tuples
end Staircase
end IterCech
end OModulePresheaf
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_OModulePresheaf_IterCech_exists_dTot_eq_single_augTot_sub_single_augCech_cup
