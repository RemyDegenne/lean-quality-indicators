@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M]

/-- A subcomodule is an existing submodule with a specified right coaction on
its subtype and a colinear inclusion. The subtype coaction is part of the data. -/
structure Subcomodule (X : RightComodule R C M) extends Submodule R M where
  /-- The right comodule on the existing submodule subtype. -/
  comodule : RightComodule R C toSubmodule
  /-- The subtype inclusion intertwines the coactions. -/
  subtype_colinear : toSubmodule.subtype.rTensor C ∘ₗ comodule.coaction =
    X.coaction ∘ₗ toSubmodule.subtype

end RightComodule
end Coalgebra
end
