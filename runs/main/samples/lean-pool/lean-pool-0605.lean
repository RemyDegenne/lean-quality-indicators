section

@[expose] public section

noncomputable section

namespace NavierStokes.ActivationBounds

open Set Filter MeasureTheory Metric ProfileHistories StressActivation

open scoped Topology ContDiff

namespace NaturalOverlap

open ReferencePath

variable (N : ReferencePath.Input)

theorem reference_histories_independent {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₁R : 2 * δ₁ < rampLimit)
    (hδ₂ : 0 < δ₂) (hδ₂R : 2 * δ₂ < rampLimit)
    (P0 : ℝ → ℝ) (hP0 : ContDiff ℝ ∞ P0) (r : HistoryRow)
    {p : Point} (hη : p.2 ∈ parameterInterval) (hX : 0 ≤ p.1)
    (hp₁ : p.1 ≤ radius N.endpoint δ₁) (hp₂ : p.1 ≤ radius N.endpoint δ₂) :
    profileHistory (N.histories hδ₁ hδ₁R P0 hP0) r p =
      profileHistory (N.histories hδ₂ hδ₂R P0 hP0) r p := by
  let A := N.histories hδ₁ hδ₁R P0 hP0
  let B := N.histories hδ₂ hδ₂R P0 hP0
  have h0 : profileInitial A r p.2 = profileInitial B r p.2 :=
    profileInitial_congr A B (fun _ => rfl) r p.2
  have hf : ∀ x ∈ Icc (0 : ℝ) p.1, A.f (x, p.2) = B.f (x, p.2) := by
    intro x hx
    exact (N.refF_eq_natural hδ₁ hδ₁R (p := (x, p.2)) hη (hx.2.trans hp₁)).trans
      (N.refF_eq_natural hδ₂ hδ₂R (p := (x, p.2)) hη (hx.2.trans hp₂)).symm
  have hu : ∀ x ∈ Icc (0 : ℝ) p.1, A.U (x, p.2) = B.U (x, p.2) := by
    intro x hx
    exact (N.refU_eq_natural hδ₁ hδ₁R (p := (x, p.2)) hη (hx.2.trans hp₁)).trans
      (N.refU_eq_natural hδ₂ hδ₂R (p := (x, p.2)) hη (hx.2.trans hp₂)).symm
  exact profileHistory_congr_up_to A B r hX h0 hf hu

end NaturalOverlap
end NavierStokes.ActivationBounds
end
end
end
