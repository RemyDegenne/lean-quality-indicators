namespace P2MW.S_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles

set_option autoImplicit false

set_option maxHeartbeats 3200000

set_option maxSynthPendingDepth 3

set_option synthInstance.maxHeartbeats 1600000

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_FujisakiC2a

set_option autoImplicit false

p2m_open

open NumberField.Units NumberField.Units.dirichletUnitTheorem MeasureTheory Topology

open scoped NNReal Classical

noncomputable section

namespace M4aLocalCFT

namespace FujisakiC2a

variable {F : Type} [Field F] [NumberField F]

def fiberCompact (F : Type) [Field F] [NumberField F] : Set ↥(fiberGroup F) :=
  Subtype.val ⁻¹' (asm ∅ '' paramSet (boundR F))

end FujisakiC2a
end M4aLocalCFT
end
end Fold_FujisakiC2a
end P2MW.S_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
