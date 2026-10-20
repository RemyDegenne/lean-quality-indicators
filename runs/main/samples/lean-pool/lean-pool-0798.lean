@[expose] public section

noncomputable section

namespace NavierStokes.PhysicalResidualNaturality

open Set Filter

open scoped Topology ComplexConjugate

open HarmonicCalculus HarmonicFields

variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace FrameOn

variable {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
  {g : HarmonicResidual.Frame D} {r : HarmonicResidual.Frame E}

theorem inverseRadiusSq (H : FrameOn U e c l g r) (hl : l ≠ 0) :
    CoefficientsOn U e (l*l)
      (constantCoefficient (fun x => (((g.radius x)^2)⁻¹ : ℝ) : D → ℂ))
      (constantCoefficient (fun x => (((r.radius x)^2)⁻¹ : ℝ) : E → ℂ)) := by
  apply CoefficientsOn.boundConstant
  intro x hx
  have hrad : ((g.radius x)^2)⁻¹ = (l*l) * ((r.radius (e x))^2)⁻¹ := by
    rw [H.radius x hx, mul_pow, mul_inv_rev]
    calc
      _ = (l^2 * (l^2)⁻¹) * (g.radius x ^ 2)⁻¹ := by
        rw [mul_inv_cancel₀ (pow_ne_zero 2 hl), one_mul]
      _ = _ := by ring
  simpa only [Complex.real_smul, ← Complex.ofReal_mul] using congrArg Complex.ofReal hrad

end FrameOn
end NavierStokes.PhysicalResidualNaturality
end
end
