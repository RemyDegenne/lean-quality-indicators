namespace P2MW.S_ModularCurve_isSeparable_jqNModC_of_modularPolynomialFamily

noncomputable section

open HahnSeries Polynomial IntermediateField

namespace ModularCurve

p2m_open

namespace SepFibre

section roots

variable (K : Type*) [Field K] {N : ℕ} [hN : Fact N.Prime] (data : ModularPolynomialData N)

variable (hsymm : EvalSymm data.Φ) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)

theorem root_succ (b : Fin N) : root K ζ b.succ = qTwist (ζ ^ (b : ℕ)) (jqModC K) := rfl

end roots
end SepFibre
end ModularCurve
end
end P2MW.S_ModularCurve_isSeparable_jqNModC_of_modularPolynomialFamily
