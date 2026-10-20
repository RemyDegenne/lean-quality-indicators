@[expose] public section

universe u v w z

namespace IsCoveringMap

section Extension

variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  {p : E → B} {q : F → B} (covp : IsCoveringMap p) (covq : IsCoveringMap q)
  {b : B}

@[simp] theorem fiberMapEquivOfPathConnected_id
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E) :
    covp.fiberMapEquivOfPathConnected covp e₀ ⟨ContinuousMap.id E, rfl⟩ =
      @MulActionHom.id (FundamentalGroup B (p e₀)) (p ⁻¹' {p e₀})
      (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul :=
  covp.fiberMap_id (p e₀)

end Extension
end IsCoveringMap
end
