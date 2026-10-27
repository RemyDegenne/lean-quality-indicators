namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff subst_comp_subst_apply subst_X
  coe_substAlgHom constantCoeff_subst_eq_zero)

noncomputable section

namespace ADT

section Main

variable {r : ℕ} [Fact r.Prime] {k₀ k : Type} [CommRing k₀] [CommRing k] (κ : k₀ →+* k)
  (X₀ : FormalODModule r k₀) (Φ : FormalODModule r k) (β₀ β₀' : Series k) (N : ℕ)
  (hβ₀ : FormalODModule.IsODHom Φ (X₀.map κ) β₀) (hβ₀' : FormalODModule.IsODHom (X₀.map κ) Φ β₀')
  (h₁ : β₀'.comp β₀ = Φ.act ((r : Zp2 r) ^ N)) (h₂ : β₀.comp β₀' = (X₀.map κ).act ((r : Zp2 r) ^ N))

def kap (ε : MvFormalGroup.End X₀.F) : Series k := Series.map κ ε.toPowerSeries

end Main
end ADT
end
end P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_injective_forall_exists_toPowerSeries_eq_comp_of_comp_eq_act_pow
