public section

namespace TauCeti

open _root_.Matrix

universe u

section Field

variable (F : Type u) [Field F]

namespace GL2Borel

variable {F}

variable (F)

theorem le_of_isSolvable_of_infinite [Infinite F]
    (P : Subgroup (GL (Fin 2) F)) [Group.IsSolvable P]
    (hBP : GL2Borel F ≤ P) : P ≤ GL2Borel F := by
  exact Subgroup.le_of_isSolvable_of_not_isSolvable_of_notMem_imp_mem_doubleCoset
    (GL2Borel F) P (GL2WeylElement F)
    (Matrix.GeneralLinearGroup.not_isSolvable_fin_two_of_infinite F)
    mem_doubleCoset_weyl_of_notMem hBP

end GL2Borel
end Field
end TauCeti
end
