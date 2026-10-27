public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

namespace Setup

variable {S : A7Base X} (C : Setup S)

theorem v_t : C.D₁.v * S.t * C.D₁.v⁻¹ = S.t * C.F.kF := C.hact.2.1

end Setup
end Sec7
end CFSG.ComponentClassification.HSFLit
end
