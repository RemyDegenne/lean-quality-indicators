@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace KTheory

variable (R : Type u) [Ring R]

attribute [local instance] directSumCartesian

attribute [local instance] directSumBraided

attribute [local instance] directSumSymmetric

attribute [local instance] smallAdditiveSkeleton

namespace K0

variable (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]

/-- The group-completion universal property: additive maps from the class
monoid to any additive commutative group extend uniquely to K₀. -/
noncomputable def lift {G : Type w} [AddCommGroup G] :
    (ProjectiveClass R →+ G) ≃ (K0 R →+ G) :=
  Algebra.GrothendieckAddGroup.lift

end K0
end KTheory
end
