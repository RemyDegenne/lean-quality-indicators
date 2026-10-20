section

@[expose] public section

noncomputable section

namespace EulerLpTranslation.SmoothL2Field

open MeasureTheory ContinuousLinearMap EulerSmoothLimit

open scoped ContDiff

universe u v

theorem jetField_toLp {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : SmoothL2Field V) (n : ℕ) : (jetField n A).toLp = A.jetLp n := by
  apply Lp.ext
  filter_upwards [(jetField n A).toLp_ae, A.jetLp_ae n] with x h₁ h₂
  exact h₁.trans ((jetField_field A n x).trans h₂.symm)

end EulerLpTranslation.SmoothL2Field
end
end
end
