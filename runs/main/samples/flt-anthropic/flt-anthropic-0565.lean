namespace P2MW.S_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData

noncomputable section

open HahnSeries Polynomial IntermediateField

namespace ModularCurve

p2m_open

namespace SepFibre

section roots

variable (K : Type*) [Field K] {N : ℕ} [hN : Fact N.Prime] (data : ModularPolynomialData N)

variable (hsymm : EvalSymm data.Φ) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)

include hsymm hζ in

theorem slice_jqModC_separable_of_prim : (slice data.Φ (jqModC K)).Separable := by
  rw [← separable_map (qExpand K N), slice_map]
  exact slice_jqNModC_separable K data hsymm ζ hζ

end roots
end SepFibre
end ModularCurve
end
end P2MW.S_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData
