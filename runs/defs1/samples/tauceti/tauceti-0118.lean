public noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField MonoidAlgebra

open scoped NumberField Pointwise

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- The valuation tuple of an `S`-unit, written additively as a vector in the free module on
the primes above `S`. -/
def sUnitsValuation (S : Finset (HeightOneSpectrum (𝓞 K))) :
    sUnitsRep L (↑S : Set _) ⟶
      Rep.ofMulAction ℤ (L ≃ₐ[K] L) ↥(primesAbove (𝓞 K) (𝓞 L) ↑S) := by
  classical
  letI := (primesAbove_finite (𝓞 K) (𝓞 L) S.finite_toSet).to_subtype
  let e : Additive (↥(primesAbove (𝓞 K) (𝓞 L) ↑S) → Multiplicative ℤ) ≃ₗ[ℤ]
      (↥(primesAbove (𝓞 K) (𝓞 L) ↑S) → ℤ) :=
    (MulEquiv.funMultiplicative _ ℤ).symm.toAdditiveLeft.toIntLinearEquiv
  let v := (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) ↑S) L).toAdditive.toIntLinearMap
  let q := (Finsupp.linearEquivFunOnFinite ℤ ℤ
    ↥(primesAbove (𝓞 K) (𝓞 L) ↑S)).symm.toLinearMap
  let r : (↥(primesAbove (𝓞 K) (𝓞 L) ↑S) →₀ ℤ) →ₗ[ℤ]
      MonoidAlgebra ℤ ↥(primesAbove (𝓞 K) (𝓞 L) ↑S) :=
    (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap
  let f := r ∘ₗ q ∘ₗ e.toLinearMap ∘ₗ v
  exact Rep.ofHom ⟨f, by
    intro σ
    ext u w
    simp only [LinearMap.comp_apply, Representation.coeff_ofMulAction]
    -- The four linear equivalences defining `f` reduce its coefficients to `unitValuation`.
    change Multiplicative.toAdd
        (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) ↑S) L (σ • u.toMul) w) =
      Multiplicative.toAdd
        (Set.unitValuation (primesAbove (𝓞 K) (𝓞 L) ↑S) L u.toMul (σ⁻¹ • w))
    have h := valuationOfNeZero_smul_primesAbove (↑S : Set _) σ (σ⁻¹ • w) u.toMul
    simpa only [Set.unitValuation_apply, smul_inv_smul,
      GlobalNumberFields.coe_smul_unit_primesAbove] using congrArg Multiplicative.toAdd h⟩

end TauCeti.ClassFieldTheory
end
