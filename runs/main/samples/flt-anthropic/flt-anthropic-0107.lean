namespace P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero

set_option autoImplicit false

namespace WeierstrassCurve

p2m_open

namespace M5HD2

theorem psCoeff_eq {R : Type*} [CommRing R] (n : ℕ) (f : PowerSeries R) :
    PowerSeries.coeff n f = MvPowerSeries.coeff (Finsupp.single () n) f := by
  rw [PowerSeries.coeff_def (s := Finsupp.single () n) (Finsupp.single_eq_same)]

end M5HD2
end WeierstrassCurve
end P2MW.S_WeierstrassCurve_exists_map_fstHom_eq_and_snd_coeff_nthSeries_ne_zero
