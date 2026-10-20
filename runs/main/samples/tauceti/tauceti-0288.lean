public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}

variable {A : Type*} [TopologicalSpace A]

open _root_.FundamentalGroup

lemma _root_.IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply_coe [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e e' : p ⁻¹' {x}) :
    (hp.monodromy ((IsCoveringMap.fundamentalGroupEquivFiber hp e).symm e').toPath e : E) = e' := by
  exact congrArg Subtype.val (IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply hp e e')

end TauCeti
end
