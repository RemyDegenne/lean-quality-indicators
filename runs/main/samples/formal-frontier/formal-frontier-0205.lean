@[expose] public section

universe u v w

open CategoryTheory

namespace ModuleCat

variable (R : Type u) [Ring R]

namespace FiniteProjective

section Representatives

variable (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

variable (Q : Type w) [AddCommGroup Q] [Module R Q]
  [Module.Finite R Q] [Module.Projective R Q]

@[simp]
theorem reprIsoOfLinearEquiv_inv_apply (e : P ≃ₗ[R] Q) (x : repr R Q) :
    homLinearEquiv R _ _ (reprIsoOfLinearEquiv R P Q e).inv x =
      (reprEquiv R P).symm (e.symm (reprEquiv R Q x)) := rfl

end Representatives
end FiniteProjective
end ModuleCat
end
