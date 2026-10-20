namespace P2MW.S_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne

set_option autoImplicit false

open IsLocalRing ModularCurve ModularCurve.UVCrossingModel

namespace L1BUV

section General

variable {W k : Type} [CommRing W] [CommRing k] (ρ : W →+* k)

noncomputable def brHom : MvPowerSeries (Fin 2) W →+* PowerSeries k where
  toFun f := PowerSeries.mk fun n => ρ (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n) f)
  map_one' := by
    classical
    ext n
    rw [PowerSeries.coeff_mk, MvPowerSeries.coeff_one, PowerSeries.coeff_one]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [if_neg (by rwa [Finsupp.single_eq_zero]), if_neg hn, map_zero]
  map_mul' f g := by
    classical
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single,
      Finset.sum_map, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd,
      PowerSeries.coeff_mk, map_mul]
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

end General
end L1BUV
end P2MW.S_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
