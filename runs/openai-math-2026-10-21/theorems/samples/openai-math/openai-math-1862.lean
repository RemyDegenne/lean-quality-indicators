namespace OAI

noncomputable section

namespace Rokhlin

namespace ArrayObjects.Object.Rolled

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp

universe u

variable {I : Type u} [Fintype I] [DecidableEq I] {X : StandardSpace.{u}} {T : X ≃ᵐ X}
    {base : InitialLaws I X T} (M : Object I base)

lemma raw_diagonal_binary (hM : M.IsSaturated) (hk : 3 ≤ Fintype.card I) (i : I) :
    ∀ᵐ u ∂M.parameterLaw 0,
    ∀ᵐ pq ∂(M.parameterCoordinateKernel i u).prod (M.parameterCoordinateKernel i u),
    ∀ (f : I → Arr I M.Y 0 → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 pq.1, ∏ j, f j (plane 0 0 j y) = c) →
      let v := circleLp (M.ownKernel 0 u) (f i) (hf i)
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = 0 ∨
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = v := by
  let P : Arr I M.U 0 → (Arr I M.U 1 × Arr I M.U 1) → Prop := fun u pq =>
    ∀ (f : I → Arr I M.Y 0 → Circle) (hf : ∀ j, Measurable (f j)) (c : Circle),
      (∀ᵐ y ∂M.ownKernel 1 pq.1, ∏ j, f j (plane 0 0 j y) = c) →
      let v := circleLp (M.ownKernel 0 u) (f i) (hf i)
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = 0 ∨
      (rawSlotActive M i (M.ownKernel 0 u) pq.2).starProjection v = v
  have h := conditional_ae_descent (P := P)
    ((measurable_plane 0 0 i).comp (measurable_plane 1 0 i))
    ((measurable_plane _ _ _).prodMk (measurable_plane _ _ _))
    (M.diagonal_parameter_product hM (by omega) i) (raw_row_line_projection M hM hk i i)
  rw [←Measure.map_map (measurable_plane 0 0 i) (measurable_plane 1 0 i),
    M.parameterLaw_consistent 1 0 i,M.parameterLaw_consistent 0 0 i] at h
  simpa only [Kernel.prod_apply] using h

end ArrayObjects.Object.Rolled
end Rokhlin
end
end OAI
