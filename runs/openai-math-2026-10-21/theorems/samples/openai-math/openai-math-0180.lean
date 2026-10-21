namespace OAI

section

namespace Erdos3

theorem annihilating_coordinate_difference_dvd {I : Type*} [DecidableEq I]
    (χ : AddChar (I → ℤ) ℂ) (v : I → ℤ) (i : I) {x y : ℤ}
    (hxy : χ (Function.update v i x) = χ (Function.update v i y)) :
    (orderOf (latticeCharacterCoordinates χ i) : ℤ) ∣ x - y := by
  have hn : χ (Function.update v i y) ≠ 0 := (χ.val_isUnit _).ne_zero
  have hd : χ (Function.update v i x - Function.update v i y) = 1 := by
    rw [χ.map_sub_eq_div, hxy, div_self hn]
  rw [update_integerVector_sub, χ.map_zsmul_eq_zpow] at hd
  change latticeCharacterCoordinates χ i ^ (x - y) = 1 at hd
  let u := (χ.val_isUnit (Pi.single i 1)).unit
  have hu : (u : ℂ) = latticeCharacterCoordinates χ i := (χ.val_isUnit _).unit_spec
  have hpow : u ^ (x - y) = 1 := by
    apply Units.ext
    simpa only [Units.val_zpow_eq_zpow_val, hu, Units.val_one] using hd
  have hdiv := orderOf_dvd_iff_zpow_eq_one.mpr hpow
  rwa [← orderOf_units, hu] at hdiv

end Erdos3
end
end OAI
