@[expose] public section

local macro_rules | `($x ^ $n:num) => `($x ^ ($n : ℕ))

noncomputable section

namespace NavierStokes.ActivationCone

open Set Filter

open scoped Topology ContDiff

open ConeAlgebra StressActivation ProfileHistories

theorem natural_reference_bounds {h j σ Λ C : ℝ} {P0 : ℝ → ℝ}
    {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (hΛ : 0 < Λ) (F : NaturalEntrance.EntranceProfile d Λ C)
    {δ : ℝ} (hδ : 0 < δ) (hδlim : 2 * δ < ReferencePath.rampLimit) :
    let N := ReferencePath.Input.ofNatural hΛ F.profile.family
    let A := referenceP1 (FromReference.refLog N δ)
    let B := referenceP2 N.endpoint (FromReference.refLog N δ) (FromReference.refAxial N δ)
    ∃ τ α M : ℝ, 0 < τ ∧ τ ≤ δ ∧ 0 < α ∧ 1 ≤ M ∧
      ∀ y ∈ Icc (0 : ℝ) τ, ∀ η ∈ Icc (-1 : ℝ) 1,
        α ≤ A (y, η) ∧ 2 + 1 / 8 < A (y, η) + B (y, η) ^ 2 / A (y, η) ∧
        A (y, η) + B (y, η) ^ 2 / A (y, η) ≤ M ∧
        |B (y, η)| ≤ M ∧ |B (y, η) / A (y, η)| ≤ M ∧ |B (y, η) ^ 2 / A (y, η)| ≤ M := by
  let N := ReferencePath.Input.ofNatural hΛ F.profile.family
  let A := referenceP1 (FromReference.refLog N δ)
  let B := referenceP2 N.endpoint (FromReference.refLog N δ) (FromReference.refAxial N δ)
  have hsub : Icc (0 : ℝ) δ ×ˢ Icc (-1 : ℝ) 1 ⊆
      (logDomain ReferencePath.parameterInterval ReferencePath.parameterInterval_open).carrier :=
    fun p hp => ⟨mem_univ _, NaturalAxisCoefficients.original_interval_interior hp.2⟩
  apply compact_reference_bounds isCompact_Icc hδ (by norm_num : (0 : ℝ) < 1 / 8)
    ((referenceP1_smooth N hδ hδlim).continuousOn.mono hsub)
    ((referenceP2_smooth N hδ hδlim).continuousOn.mono hsub)
  · intro p hp
    rw [referenceP1_natural N hδ hδlim hp.1.2 (NaturalAxisCoefficients.original_interval_interior
        hp.2)]
    apply F.slope_positive
    · change (Λ * (N.fromLog p).1, p.2) ∈ NaturalEntrance.entranceSet
      have he : Real.exp p.1 < 41 / 40 := by
        have hy : p.1 < ReferencePath.rampLimit := by linarith only [hδ, hδlim, hp, hp.1.2]
        simpa only [ReferencePath.rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)]
          using Real.exp_lt_exp.mpr hy
      have hid : Λ * (N.fromLog p).1 = 4 * Real.exp p.1 := N.fromLog_scaled p
      exact ⟨⟨by rw [hid]; positivity, by rw [hid]; linarith only [he]⟩, hp.2⟩
    · exact mul_pos N.endpoint_pos (Real.exp_pos p.1)
  · intro η hη
    rw [referenceP1_natural N hδ hδlim (by
        linarith only [hδ]) (NaturalAxisCoefficients.original_interval_interior hη),
      referenceP2_natural N hδ hδlim (by
          linarith only [hδ]) (NaturalAxisCoefficients.original_interval_interior hη)]
    have hm := F.cone_margin η hη
    rw [show (2 + 2 * (1 / 8) : ℝ) = 9 / 4 by norm_num]
    simpa only [NaturalEntrance.coneSize, ReferencePath.Input.fromLog, Real.exp_zero,
      mul_one, N, ReferencePath.Input.endpoint, ReferencePath.Input.ofNatural] using hm.le

end NavierStokes.ActivationCone
end
end
