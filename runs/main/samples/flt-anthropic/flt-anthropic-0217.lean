namespace P2MW.S_QuaternionAlgebra_IsOrder_relIndex_finiteIdeleStabilizer_inf_map_conj_eq_local

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped TensorProduct Quaternion Pointwise

open IsDedekindDomain NumberField

namespace HeckeLocal

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  rw [box_eq_span]; rfl

end HeckeLocal
end P2MW.S_QuaternionAlgebra_IsOrder_relIndex_finiteIdeleStabilizer_inf_map_conj_eq_local
