namespace P2MW.S_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing

set_option autoImplicit false

universe u v

noncomputable section

namespace P2mKcCartierFull

open MvPowerSeries

section OrdIdeal

variable {R : Type*} [CommRing R] {σ τ : Type*}

theorem ordIdeal_antitone {m n : ℕ} (h : m ≤ n) : ordIdeal τ R n ≤ ordIdeal τ R m :=
  fun _ ha => le_trans (ENat.coe_le_coe.mpr h) ha

end OrdIdeal
end P2mKcCartierFull
end
end P2MW.S_MvFormalGroup_CartierModule_exists_hom_map_eq_of_perfectRing
