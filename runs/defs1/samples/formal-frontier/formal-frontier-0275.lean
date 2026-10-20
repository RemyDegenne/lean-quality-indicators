public section

set_option warningAsError true

namespace MvPowerSeries

variable {σ R : Type*} [CommRing R]

/-- The canonical linear extension of any polynomial endomorphism to restricted series.
Completeness is required only for the coefficient ring, not the restricted-series ring. -/
noncomputable def restrictedLinearExtension (I : Ideal R) [IsAdicComplete I R]
    (F : MvPolynomial σ R →ₗ[R] MvPolynomial σ R) :
    adicallyRestrictedSubring (σ := σ) I →ₗ[R]
      adicallyRestrictedSubring (σ := σ) I where
  toFun := restrictedLinearExtensionFun I F
  map_add' f g := by
    apply restricted_eq_of_reductions I
    intro n
    simp only [adicReduction_restrictedLinearExtensionFun, map_add]
  map_smul' r f := by
    apply restricted_eq_of_reductions I
    intro n
    rw [adicReduction_restrictedLinearExtensionFun]
    simp only [RingHom.id_apply]
    rw [← linearAdicReduction_apply I n (r • f),
      ← linearAdicReduction_apply I n (r • restrictedLinearExtensionFun I F f)]
    rw [(linearAdicReduction I n).map_smul r f,
      (linearAdicReduction I n).map_smul r (restrictedLinearExtensionFun I F f)]
    simp only [linearAdicReduction_apply, adicReduction_restrictedLinearExtensionFun]
    exact (polynomialLinearMapMod I n F).map_smul_of_tower r _

end MvPowerSeries
end
