public noncomputable section

open scoped NNReal

open unitInterval MulOpposite

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace MooreReplacement

/-- The **transitive lifting function** of the endpoint map of the Moore-path replacement:
concatenation, `((e, γ), δ) ↦ (s ↦ (e, γ · δ|[0, s]))`. -/
def endpointLiftingFunction (p : C(E, B)) : MooreLiftingFunction (endpoint p) where
  toContinuousMap := ⟨fun y ↦ liftPath y.point y.path y.source_path, by
    refine MoorePath.continuous_iff.2 ⟨?_, ?_⟩
    · simp only [length_liftPath]
      exact MoorePath.continuous_length.comp continuous_path
    simp only [liftPath_apply]
    exact continuous_mk (continuous_point.comp (continuous_point.comp continuous_fst))
      ((continuous_path.comp (continuous_point.comp continuous_fst)).moorePath_trans
        ((continuous_path.comp continuous_fst).moorePath_truncate continuous_snd) _) _⟩
  source_apply' y := source_liftPath _ _ y.source_path
  map_apply' y := map_liftPath _ _ y.source_path

end MooreReplacement
end TauCeti
end
