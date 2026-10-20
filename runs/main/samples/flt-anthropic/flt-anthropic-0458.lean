namespace P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_five

set_option autoImplicit false

theorem solution (j : ℕ) : ModularCurve.SharpUnitNecessary (12 * j + 5) :=
  DedekindEtaLog.sharpUnitNecessary_of_mod_twelve_eq_five j

end P2MW.S_ModularCurve_sharpUnitNecessary_of_mod_twelve_eq_five
