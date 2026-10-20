section

@[expose] public section

noncomputable section

open scoped BigOperators BoundedContinuousFunction

namespace EulerBoundedFieldCalculus

variable {α ι : Type*} [TopologicalSpace α] [Fintype ι]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

local instance instBoundedFieldMultilinear1 (i : ι) : NormedAddCommGroup (α →ᵇ V i) := inferInstance

local instance instBoundedFieldMultilinear2 (i : ι) : NormedSpace ℝ (α →ᵇ V i) := inferInstance

local instance instBoundedFieldMultilinear3 : NormedAddCommGroup (α →ᵇ W) := inferInstance

local instance instBoundedFieldMultilinear4 : NormedSpace ℝ (α →ᵇ W) := inferInstance

/-- Multilinear algebra as an element of `MultilinearMap ℝ (fun i => α →ᵇ V i) (α →ᵇ W)`. -/
def multilinearAlgebra (L : ContinuousMultilinearMap ℝ V W) :
    MultilinearMap ℝ (fun i => α →ᵇ V i) (α →ᵇ W) := by
  classical
  refine MultilinearMap.mk' (multilinearValue L) ?_ ?_
  · intro f i a b
    apply BoundedContinuousFunction.ext
    intro x
    have he (c : α →ᵇ V i) :
        (fun j => Function.update f i c j x) =
          Function.update (fun j => f j x) i (c x) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    simp only [BoundedContinuousFunction.add_apply, multilinearValue_apply, he]
    exact L.map_update_add _ _ _ _
  · intro f i r a
    apply BoundedContinuousFunction.ext
    intro x
    have he (c : α →ᵇ V i) :
        (fun j => Function.update f i c j x) =
          Function.update (fun j => f j x) i (c x) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    simp only [BoundedContinuousFunction.smul_apply, multilinearValue_apply, he]
    exact L.map_update_smul _ _ _ _

end EulerBoundedFieldCalculus
end
end
end
