public section

noncomputable section

open TauCeti

open scoped ENNReal

namespace ContinuousLinearMap

section NormedField

variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

variable {p}

theorem enorm_toLp_le_summingENorm_mul_of_ne_top {T : E →L[𝕜] F}
    (hT : T.summingENorm p ≠ ∞) {ι : Type*} [Fintype ι] (x : ι → E) :
    ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ ≤
      T.summingENorm p * ENNReal.ofReal (weakLpNorm (𝕜 := 𝕜) p x) := by
  let e := Fintype.equivFin ι
  have h := (summingENorm_le_iff hT).1 le_rfl _ (x ∘ e.symm)
  have hn : ‖WithLp.toLp p (fun i ↦ T ((x ∘ e.symm) i))‖ₑ =
      ‖WithLp.toLp p (fun i ↦ T (x i))‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact congrArg _ (PiLp.norm_toLp_comp_equiv e.symm fun i ↦ T (x i))
  rwa [weakLpNorm_comp_equiv, hn] at h

end NormedField
end ContinuousLinearMap
end
end
