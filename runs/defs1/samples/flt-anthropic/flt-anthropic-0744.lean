namespace P2MW.S_ModularCurve_hasSum_sharpUnitSeries_qParam

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function HahnSeries

open scoped MatrixGroups ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

p2m_open

namespace EIT

variable (ℓ : ℕ)

variable [NeZero ℓ]

def divNat (τ : ℍ) : ℍ :=
  ⟨(τ : ℂ) / ℓ, by
    rw [Complex.div_natCast_im]
    exact div_pos τ.2 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne ℓ)))⟩

end EIT
end ModularCurve
end
end P2MW.S_ModularCurve_hasSum_sharpUnitSeries_qParam
