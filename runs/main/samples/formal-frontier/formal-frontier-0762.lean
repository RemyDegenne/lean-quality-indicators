@[expose] public section

universe u v w z

namespace IsCoveringMap

section Extension

variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  {p : E → B} {q : F → B} (covp : IsCoveringMap p) (covq : IsCoveringMap q)
  {b : B}

@[simp] theorem fiberMapEquiv_symm_id [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B) :
    (covp.fiberMapEquiv covp b).symm (@MulActionHom.id (FundamentalGroup B b) (p ⁻¹' {b})
      (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul) = ⟨ContinuousMap.id E, rfl⟩ := by
  apply (covp.fiberMapEquiv covp b).symm_apply_eq.mpr
  exact (covp.fiberMapEquiv_id b).symm

end Extension
end IsCoveringMap
end
