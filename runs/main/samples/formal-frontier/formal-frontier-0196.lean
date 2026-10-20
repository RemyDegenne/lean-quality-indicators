@[expose] public section

universe u

namespace HSpace

variable {X : Type u} [TopologicalSpace X] [HSpace X]

@[simp]
theorem loopMul_apply (p q : Path (HSpace.e : X) HSpace.e) (t : unitInterval) :
    loopMul p q t = HSpace.hmul (p t, q t) := rfl

end HSpace
end
