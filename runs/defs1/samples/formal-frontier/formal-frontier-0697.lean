set_option warningAsError true

@[expose] public section

open MeasureTheory Set

universe u v

namespace ContinuousMap

variable {X : Type u} {F : Type v} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup F]
  (μ : Measure X) [IsFiniteMeasure μ]

variable [NormedSpace ℂ F] [CompleteSpace F]

/-- The linear map underlying Bochner integration of continuous functions. -/
noncomputable def integralLinearMap : C(X, F) →ₗ[ℂ] F where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := by
    simpa only [ContinuousMap.coe_add, Pi.add_apply] using
      (integral_add (integrable μ f) (integrable μ g))
  map_smul' c f := by
    simp only [ContinuousMap.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact integral_smul c (fun x => f x)

end ContinuousMap
end
