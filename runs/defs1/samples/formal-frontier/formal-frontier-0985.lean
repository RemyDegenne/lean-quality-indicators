@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

namespace RightComodule

variable {R : Type u} {C : Type v} {M : Type w}

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M]

namespace Subcomodule

variable {X : RightComodule R C M}

/-- Inclusion of a subcomodule as a bundled right-comodule morphism. -/
def subtype (U : X.Subcomodule) : RightComoduleHom U.comodule X where
  toLinearMap := U.toSubmodule.subtype
  colinear := U.subtype_colinear.symm

end Subcomodule
end RightComodule
end Coalgebra
end
