namespace P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul

set_option autoImplicit false

open ModularCurve ModularCurve.UVCrossingModel

namespace KummerClass44

open KummerNorm44

section Twist

variable {W : Type*} [CommRing W]

variable (z : Fin 2 → W) (hz : z 0 * z 1 = 1) (c : W)

theorem twist_modelMap (n : ℕ) (hn : n ≠ 0) (hzn : z ^ n = 1) (π : W) (m : ℕ)
    (h1 : (1 : Fin 2 → W) 0 * (1 : Fin 2 → W) 1 = 1) (r : UVCrossingModel W (π ^ (m * n))) :
    twist z hz (π ^ m) (modelMap n hn 1 h1 π m r) = modelMap n hn 1 h1 π m r := by
  obtain ⟨G, rfl⟩ := UVCrossingModel.mk_surjective _ r
  rw [modelMap_mk, twist_mk]
  congr 1
  simp only [liftHom, RingHom.coe_comp, Function.comp_apply, MvPowerSeries.rescale_one, RingHom.id_apply]
  show MvPowerSeries.rescale z (MvPowerSeries.expand n hn G) = MvPowerSeries.expand n hn G
  rw [rescale_expand z n hn, hzn, MvPowerSeries.rescale_one]; rfl

end Twist
end KummerClass44
end P2MW.S_ModularCurve_UVCrossingModel_exists_pow_eq_unit_mul_U_of_isCyclic_of_isUnramifiedAt_of_residue_of_isPrimitiveRoot_mul
