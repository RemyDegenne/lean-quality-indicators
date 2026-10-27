public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

namespace CPair

variable (P : CPair S F T₁)

theorem w₁N_conj_z : P.w₁N * S.z * P.w₁N⁻¹ = S.z := by
  rw [P.w₁N_conj_E (z_mem_E _), P.V.w₁_conj_z]

end CPair
end Sec8
end CFSG.ComponentClassification.HSFLit
end
