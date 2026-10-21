namespace OAI

namespace Ostmann

open Filter

open scoped BigOperators SchwartzMap FourierTransform ComplexConjugate Classical

theorem quadraticBandMass_isLittleO
    (hBonami : PublishedBonamiBound) (P₀ : PublishedProgressionInput)
    (H : PublishedRealZeroInput P₀) (hSiegel : PublishedSiegelBound)
    (sieve : PublishedQuadraticLargeSieve) (hsize : PublishedSummandSizeBound)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (C₀ : ℝ) (hM : MertensEstimate C₀)
    (cψ Bψ : ℝ) (hcψ : 0 < cψ) (hBψ : 3 ≤ Bψ) (ψ : 𝓢(ℝ, ℂ))
    (hreal : ∀ x, conj (ψ x) = ψ x) (hψ0 : ∀ x, 0 ≤ (ψ x).re)
    (hψ1 : ∀ x ∈ Set.Icc (0 : ℝ) 1, cψ ≤ (ψ x).re)
    (hsupp : ∀ x : ℝ, Bψ ^ 2 < |x| → 𝓕 ψ x = 0) :
    (fun T => quadraticBandMass A N T) =o[atTop] (fun T : ℝ => T) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hδ : 0 < min c 1 := lt_min hc (by norm_num)
  have hh := eventual_translated_quadratic_bias_lt hBonami P₀ H hSiegel sieve hsize
    hA hB h N hN C₀ hM cψ Bψ hcψ hBψ ψ hreal hψ0 hψ1 hsupp (min c 1) hδ (min_le_right _ _)
  filter_upwards [hh, eventually_ge_atTop (0 : ℝ)] with T hh hT
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticBandMass_nonneg A N T), Real.norm_eq_abs, abs_of_nonneg hT]
  exact (hh (fun p => maximizingQuadraticTranslate (tailSupport A N p) p)).le.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hT)

end Ostmann
end OAI
