namespace P2MW.S_CohCarrier_charInvolution_comp_opFamily

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace CharInvHecke

section HeckeT

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (A : Type*) [AddCommGroup A]

open CohCarrier

theorem comp_conjL_charInvolution (R : Type*) [Semiring R] [Module R A] (φ : H1 M H A) :
    (AddMonoidHom.toMultiplicativeRight (charInvolution M H A R φ)).comp (conjL M H ℓ) =
      ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL M H ℓ)).comp
        (resK (jEquiv M H) (GammaHUpper M H ℓ) (GammaHUpper M H ℓ) (jEquiv_mem_upper_iff M H ℓ)) := by
  refine MonoidHom.ext fun γ => ?_
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply, charInvolution_apply,
    toMul_ofMul]
  congr 2
  rw [← jEquiv_apply, jEquiv_conjL]

end HeckeT
end CharInvHecke
end P2MW.S_CohCarrier_charInvolution_comp_opFamily
