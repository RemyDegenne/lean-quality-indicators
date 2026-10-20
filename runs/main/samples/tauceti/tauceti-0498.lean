public section

open HahnSeries

open scoped LaurentSeries

namespace TauCeti

variable (K : Type*) [Field K]

namespace ContinuousKaehlerDifferential

variable {K}

@[ext]
theorem hom_ext {N : Type*} [AddCommGroup N] [Module K⸨X⸩ N]
    {ℓ ℓ' : ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] N}
    (h : ℓ (D K (single 1 1)) = ℓ' (D K (single 1 1))) : ℓ = ℓ' := by
  ext ω
  rw [← equivLaurentSeries_smul_D_single_one K ω, map_smul, map_smul, h]

end ContinuousKaehlerDifferential
end TauCeti
end
