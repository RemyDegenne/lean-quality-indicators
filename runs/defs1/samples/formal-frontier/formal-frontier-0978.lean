@[expose] public section

set_option autoImplicit false

set_option relaxedAutoImplicit false

universe uR uS uT uM

namespace ModuleCat.RightExtension

section Identity

variable (R : Type uR) [Ring R]

variable (M : Type uM) [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The canonical right-linear equivalence for extension along the identity
ring homomorphism. It sends `m ⊗ r` to `op r • m`, with inverse `m ↦ m ⊗ 1`. -/
noncomputable def idLinearEquiv : Obj (RingHom.id R) M ≃ₗ[Rᵐᵒᵖ] M where
  __ := private LinearEquiv.ofLinearMap
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) (idTo R M) (idFrom R M)
    (by
      apply LinearMap.ext
      intro m
      change idTo R M (tmul (RingHom.id R) m 1) = m
      rw [idTo_tmul]
      exact one_smul Rᵐᵒᵖ m)
    (by
      apply linearMap_ext (RingHom.id R)
      intro m r
      change tmul (RingHom.id R) (idTo R M (tmul (RingHom.id R) m r)) 1 =
        tmul (RingHom.id R) m r
      rw [idTo_tmul, smul_tmul]
      simp)

end Identity
end ModuleCat.RightExtension
end
