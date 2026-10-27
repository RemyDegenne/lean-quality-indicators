namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch

attribute [-instance] instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

p2m_open

open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion

p2m_open

open scoped nonZeroDivisors

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open IsDedekindDomain NumberField Matrix

open LanglandsTunnell.CubicInduction NumberField.AdelicLevel AdelicDock

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

namespace Ws23Tw

open LanglandsTunnell.CubicInduction

structure TwCubic (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 ℚ))) where

  whittakerLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → LocalGL3 v → ℂ

  cenLoc : (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletion ℚ)ˣ →* ℂˣ
  whittakerLoc_law : ∀ v, IsGL3PsiWhittakerFn (psiLoc ψ v) (whittakerLoc v)
  spherical : ∀ v, ¬ IsBadPlace K μ v →
    IsInducedSphericalAt (inducedCoeff K μ) v (localMaximalCompact3 (𝓞 ℚ) ℚ v) (whittakerLoc v)
  levelInvariant : ∀ v, v ∉ S₀ →
    ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, whittakerLoc v (g * k) = whittakerLoc v g
  continuous : ∀ v, Continuous (whittakerLoc v)
  ne_zero : ∀ v, whittakerLoc v ≠ 0
  scalar : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) (h : LocalGL3 v),
    whittakerLoc v (Matrix.GeneralLinearGroup.scalar (Fin 3) t * h) = ((cenLoc v t : ℂˣ) : ℂ) * whittakerLoc v h
  gauge : ∀ p : HeightOneSpectrum (𝓞 ℚ), ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 p,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → whittakerLoc p h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖whittakerLoc p h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t)

end Ws23Tw
end P2MW.S_LanglandsTunnell_RankinSelberg_exists_purifier_whittakerCoefficient_eq_mul_pSlot_of_finiteFamily_arch
