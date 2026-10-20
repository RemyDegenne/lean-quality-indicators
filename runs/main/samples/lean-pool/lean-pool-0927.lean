section

@[expose] public section

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace EulerChildParticleTime

open Set SmoothTimeField

variable {K E : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

section Time

variable {T : ℝ} {hT : 0 ≤ T} [CompleteSpace E]
  {P P₁ P₂ D D₁ D₂ : SmoothTimeField (Icc (0 : ℝ) T) E E}

theorem displacement_time (hP : TimeDerivative T hT P P₁) (hD : TimeDerivative T hT D D₁) :
    TimeDerivative T hT (displacement P D) (velocity P P₁ D D₁) := by
  have h := (hP.compDisplacement hD).add hD
  apply h.congr_fields (fun _ _ => rfl)
  intro t x
  simp only [velocity,firstTerm,SmoothTimeField.add_apply,applyField_apply,compDisplacement_apply]
  abel

end Time
end EulerChildParticleTime
end
end
end
