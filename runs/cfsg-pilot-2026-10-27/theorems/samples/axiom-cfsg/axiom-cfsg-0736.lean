public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Inst

variable (I : S.Inst)

theorem zyi_eq_wV : S.z * I.yi = I.wV (1, 1, 0, 0) := by simp [wV]

end Inst
end A7Base
end CFSG.ComponentClassification.HSFLit
end
