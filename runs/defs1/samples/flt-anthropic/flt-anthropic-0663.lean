namespace P2MW.S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function HahnSeries

open scoped MatrixGroups ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

p2m_open

namespace EIT

variable (ℓ : ℕ)

def Φ (w : ℂ) : ℂ := (P w / P (w ^ ℓ)) ^ sharpExp ℓ

end EIT
end ModularCurve
end
end P2MW.S_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam
