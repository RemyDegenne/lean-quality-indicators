@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

open Metric Module Function

open scoped Manifold ContDiff RealInnerProductSpace

section StereographicProjection

variable (v : E)

variable {v}

theorem hasFDerivAt_stereoInvFunAux (v : E) :
    HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id ℝ E) 0 := by
  have h₀ : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (0 : StrongDual ℝ E) 0 := by
    convert (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    simp only [map_zero, smul_zero]
  have h₁ : HasFDerivAt (fun w : E => (‖w‖ ^ 2 + 4)⁻¹) (0 : StrongDual ℝ E) 0 := by
    convert! (hasFDerivAt_inv _).comp _ (h₀.add (hasFDerivAt_const 4 0)) <;> simp
  have h₂ : HasFDerivAt (fun w => (4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)
      ((4 : ℝ) • ContinuousLinearMap.id ℝ E) 0 := by
    convert!
      ((hasFDerivAt_const (4 : ℝ) 0).smul (hasFDerivAt_id 0)).add
        ((h₀.sub (hasFDerivAt_const (4 : ℝ) 0)).smul (hasFDerivAt_const v 0)) using 1
    ext w
    simp
  convert! h₁.smul h₂ using 1
  ext w
  simp

end StereographicProjection
end
end
