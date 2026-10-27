@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace KTheory

variable (R : Type u) [Ring R]

attribute [local instance] directSumCartesian

attribute [local instance] directSumBraided

attribute [local instance] directSumSymmetric

attribute [local instance] smallAdditiveSkeleton

namespace ProjectiveClass

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

/-- The direct-sum isomorphism class of a finite projective right module,
using its ring-universe representative. -/
@[no_expose] noncomputable def of : ProjectiveClass R :=
  (classEquiv R).symm (Additive.ofMul (ModuleCat.FiniteProjective.isoClass Rᵐᵒᵖ M))

end ProjectiveClass
end KTheory
end
