@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace KTheory

variable (R : Type u) [Ring R]

attribute [local instance] directSumCartesian

attribute [local instance] directSumBraided

attribute [local instance] directSumSymmetric

attribute [local instance] smallAdditiveSkeleton

/-- Isomorphism classes of finite projective right `R`-modules, with zero and
binary direct sum as the commutative-monoid operations, in the ring universe. -/
noncomputable def ProjectiveClass : Type u :=
  letI : Small.{u} (Additive (Skeleton (ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ))) :=
    small_map Additive.toMul
  Shrink.{u} (Additive (Skeleton (ModuleCat.FiniteProjective.{u, u} Rᵐᵒᵖ)))

end KTheory
end
