namespace P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid

set_option autoImplicit false

open groupCohomology

namespace D1Chi

section Transversal

variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V) (K : Subgroup G) (φ : K →* G) (a : V →ₗ[k] V)

abbrev RQ : Type := Quotient (QuotientGroup.rightRel K)

end Transversal
end D1Chi
end P2MW.S_HeckeCohomology_commute_heckeH1_cTop_heckeH1_conjHom_of_forall_rep_eq_monoidHom_submonoid
