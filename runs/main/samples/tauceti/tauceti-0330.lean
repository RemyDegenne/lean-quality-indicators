public noncomputable section

namespace TauCeti.FilledCover

open Filter Function Metric Set Topology ThricePuncturedSphere

open scoped OnePoint

variable {E : Type*} [TopologicalSpace E] (p : E → ThricePuncturedSphere)

variable {p} (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))

include hp hfin

@[continuity, fun_prop] theorem continuous_fillMap : Continuous (fillMap p) := by
  refine PunctureFilling.continuous_iff.2 ⟨?_, fun i => ?_⟩
  · simpa only [Function.comp_def, fillMap_incl] using
      isOpenEmbedding_toOnePoint.continuous.comp hp.continuous
  · have h : Continuous (fun w : ↥(ball (0 : ℂ) 1) =>
        (FilledPoint.sigmaEquiv p i).1.sphereCoordInv ((w : ℂ) ^ degree p i)) :=
      ((FilledPoint.sigmaEquiv p i).1.continuous_sphereCoordInv).comp
      (continuous_subtype_val.pow (degree p i))
    exact h.congr (fun w => (fillMap_disc hp hfin i w).symm)

end TauCeti.FilledCover
end
