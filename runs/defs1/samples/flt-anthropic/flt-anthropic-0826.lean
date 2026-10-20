namespace P2MW.S_CerednikDrinfeld_FormalODModule_forall_exists_subst_act_subst_varpi_eq_smul_of_type

set_option autoImplicit false

universe u

open MvPowerSeries

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "Zp2 FormalODModule SpecialFormalODModule" namespace FormalODModule p2m_export "CerednikDrinfeld.FormalODModule" "map varpi_comp_act F varpi varpi_comp_varpi isLawHom_act act_add act_one isComm act isLawHom_varpi" end CerednikDrinfeld.FormalODModule

p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.FormalODModule" in

namespace MvFormalGroup

namespace C1Kit

p2m_open

variable {g : ℕ} {R : Type*} [CommRing R] (F : MvFormalGroup g R) {Γ : MvPowerSeries (Fin g ⊕ Fin g) R}

variable {φ ψ : Fin g → MvPowerSeries (Fin g) R}

section ThreeBlocks

noncomputable abbrev B3 : Fin g → MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R := fun l => X (Sum.inr (Sum.inr l))

end ThreeBlocks
end C1Kit
end MvFormalGroup
end CerednikDrinfeld
end P2MW.S_CerednikDrinfeld_FormalODModule_forall_exists_subst_act_subst_varpi_eq_smul_of_type
