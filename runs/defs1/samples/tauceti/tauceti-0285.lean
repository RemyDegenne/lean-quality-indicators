public section

open Multiplicative Set

open scoped ContDiff Manifold

namespace TauCeti.Toric

variable {s : ℕ}
  (g : AddGeneratingFamily (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone) s)

namespace Fan

variable (Φ : Fan ((Int.castAddHom ℝ).compLeft (Fin 1))) (hΦ : Φ.IsRegular)
  (hσ : negativeRayCone ∈ Φ.cones)

/-- The negative-ray chart inclusion is a biholomorphism onto its cone open, for the standard
negative-character complex structure. -/
noncomputable def negativeRayChartPartialDiffeomorph (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := negativeRayChartedSpace g
    let _ := Φ.analyticChartedSpace hΦ
    PartialDiffeomorph 𝓘(ℂ, (Fin 1 → ℂ) × (Fin 0 → ℂ))
      𝓘(ℂ, Fin (Module.finrank ℤ (Fin 1 → ℤ)) → ℂ)
      (AffineSemigroupComplexPoint (dualSemigroup (isIntegralLattice_intCast 1) negativeRayCone))
      (Φ.analyticRealization hΦ) n :=
  Φ.analyticAffineChartPartialDiffeomorph hΦ ⟨negativeRayCone, hσ⟩
    negativeRayBasis_extends negativeRayNumbering g n

end Fan
end TauCeti.Toric
end
