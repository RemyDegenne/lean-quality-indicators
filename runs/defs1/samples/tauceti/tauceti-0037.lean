public section

open Bundle

open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E H M : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothAlmostComplexStructure

variable {J K : SmoothAlmostComplexStructure I M}

/-- A continuous endomorphism of a normed space squaring to `-1` defines a constant smooth almost
complex structure on the corresponding model manifold. -/
def const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Jc : V →L[ℝ] V) (hJc : ∀ v, Jc (Jc v) = -v) :
    SmoothAlmostComplexStructure (modelWithCornersSelf ℝ V) V where
  toEndomorphism :=
    ⟨fun _ ↦ Jc, by
      intro x
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, ?_⟩
      simpa [inCoordinates_tangent_bundle_core_model_space] using
        (contMDiffAt_const (x := x) (c := Jc))⟩
  square_neg := by
    intro x
    ext v
    -- After the composition and the negated identity are unfolded, the goal is `hJc v`: the
    -- additive group instance on `TangentSpace 𝓘(ℝ, V) x` is the one of `V` itself.
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.neg_apply,
      ContinuousLinearMap.coe_id', id_eq]
    exact hJc v

end SmoothAlmostComplexStructure
end TauCeti
end
end
