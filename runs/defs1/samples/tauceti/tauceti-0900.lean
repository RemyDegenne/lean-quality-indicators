public section

open scoped NNReal

open UniformSpace

namespace TauCeti.WittVector

open _root_.WittVector

variable (p : ℕ) [Fact p.Prime] {K O : Type*} [Field K] [CommRing O] [Algebra O K]
  {v : Valuation K ℝ≥0} {ϖ : O} [CharP O p] [PerfectRing O p]

local notation "𝕎" => _root_.WittVector p

variable {p}

section Presentation

open MvPowerSeries

variable (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ ρ₁' : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1) (hρ₁' : ρ₁' ∈ Set.Ioo 0 1)

variable {k : ℕ} (c : Fin k → ℝ) [∀ i, Fact (0 < c i)]

variable (p) in
/-- **Evaluation at `p⁻¹` onto a smaller left endpoint.** For `ρ₁ ≤ ρ₁' ≤ ρ₂`, the ring
homomorphism

```text
B^{[ρ₁, ρ₂]}{T/c, U/ρ₁'⁻¹} → B^{[ρ₁', ρ₂]}{T/c},    T ↦ T,  U ↦ p⁻¹,
```

restricting the coefficients to the subinterval. Here `U = X 0` and `T i = X i.succ`, and `U` has
radius `ρ₁'⁻¹`, the norm of `p⁻¹` in `B^{[ρ₁', ρ₂]}`. It is surjective
(`TauCeti.WittVector.intervalRingRestrictedEval_surjective`): this is the form of Kedlaya's
Lemma 4.9 that moves the left endpoint of an interval in the normalisation `λ_ρ(p) = ρ`. -/
noncomputable def intervalRingRestrictedEval (h₁ : ρ₁ ≤ ρ₁') (h₁₂ : ρ₁' ≤ ρ₂) :
    IsRestricted.subring (R := IntervalRing p hv hϖ hϖ' hρ₁ hρ₂)
        (Fin.cons (ρ₁' : ℝ)⁻¹ c : Fin (k + 1) → ℝ) →+*
      IsRestricted.subring (R := IntervalRing p hv hϖ hϖ' hρ₁' hρ₂) c :=
  MvPowerSeries.restrictedEval₂
    ((algebraMap _ _).comp
      (intervalRingRestrict p hv hϖ hϖ' hρ₁ hρ₂ hρ₁' hρ₂ h₁ h₁₂ le_rfl).toRingHom)
    (Fin.cons (algebraMap _ _ (Ring.inverse (p : IntervalRing p hv hϖ hϖ' hρ₁' hρ₂)))
      fun i ↦ ⟨X i, isRestricted_monomial c (Finsupp.single i 1) 1⟩)
    (fun b ↦ by
      simpa using norm_intervalRingRestrict_le h₁ h₁₂ le_rfl b)
    (Fin.cases (by
      have h : ((ρ₂ : ℝ))⁻¹ ≤ (ρ₁' : ℝ)⁻¹ :=
        inv_anti₀ (by exact_mod_cast hρ₁'.1) (by exact_mod_cast h₁₂)
      simpa using h) fun i ↦ by simp)

end Presentation
end TauCeti.WittVector
end
