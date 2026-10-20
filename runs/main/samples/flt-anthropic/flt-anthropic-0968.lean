namespace P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace NodeRingSol

section Chart

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

variable {K : Type} [CommRing K]

open IsLocalRing

variable {q : ℕ} {a ϖ π : O} {f u v : MvPowerSeries (Fin 2) O} {πK : MvPowerSeries (Fin 2) O →+* K} {rg : Set K}
  {x y w : K}

namespace Setup

variable (S : Setup q a ϖ π f u v πK rg x y w)

include S

theorem RepAt.mono {n n' : ℕ} (h : n ≤ n') {r : K} (hr : S.RepAt n r) : S.RepAt n' r := by
  obtain ⟨m, hm, hrm⟩ := hr
  refine ⟨m * X 0 ^ (n' - n), ?_, ?_⟩
  · have := hm.mul (vanBelow_X_pow (κ := ResidueField O) 0 (n' - n))
    rw [show n + (n' - n) = n' by omega] at this
    simpa [map_mul, map_pow, MvPowerSeries.map_X] using this
  · rw [map_mul, map_pow, ← S.hy, ← hrm, mul_assoc, ← pow_add, show n + (n' - n) = n' by omega]

end Setup
end Chart
end NodeRingSol
end
end P2MW.S_DrinfeldCurve_LocalChart_exists_isMaximal_ringEquiv_adicCompletion_atPrime_uvCrossingModel_pow_of_mem_maximalIdeal
