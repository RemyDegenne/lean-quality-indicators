namespace P2MW.S_ModularForm_etaProductEleven_fricke

set_option autoImplicit false

p2m_open

open UpperHalfPlane hiding I

open scoped Real ModularForm MatrixGroups Topology Manifold

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

noncomputable section

namespace ModularCurve

lemma deltaEleven_coe :
    ⇑deltaEleven = fun τ : ℍ => deltaGamma0 (ModularForm.heckeDiagMatrix 11 • τ) :=
  (CuspForm.exists_degeneracy_Gamma0 (N := 11) eleven_mul_one_dvd deltaGamma0).choose_spec

end ModularCurve
end
end P2MW.S_ModularForm_etaProductEleven_fricke
