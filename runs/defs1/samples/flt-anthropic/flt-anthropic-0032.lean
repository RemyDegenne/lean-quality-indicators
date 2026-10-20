namespace P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic

namespace FinFlatHopf p2m_export "FinFlatHopf" "not_isLocalRing_dual_of_isLocalRing inertiaFixed_valuationSubring_dvr_fixer_le_inertia dualPoints_equiv_monoidHom" end FinFlatHopf

p2m_open_scoped "FinFlatHopf" in

set_option autoImplicit false

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

p2m_reactivate

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

p2m_open_scoped "FinFlatHopf" in

open Pointwise

p2m_open_scoped "FinFlatHopf" in

open scoped TensorProduct

p2m_open_scoped "FinFlatHopf" in

p2m_open_scoped "FinFlatHopf" in

p2m_open_scoped "FinFlatHopf" in

set_option autoImplicit false

p2m_reactivate

set_option autoImplicit false

p2m_reactivate

set_option autoImplicit false

noncomputable section

namespace FinFlatHopf

namespace W4

p2m_open

p2m_reactivate

p2m_reactivate

section scal

variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
  (u : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Rˣ)
  (IP : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

abbrev moduleScal : Module (Scal R M u IP) M :=
  letI := moduleRbar R M
  Module.compHom M (scalSubring R M u IP).subtype

end scal
end W4
end FinFlatHopf
end
end FinFlatHopf
end P2MW.S_FinFlatHopf_exists_subgroup_inertia_trivial_quotient_cyclotomic
