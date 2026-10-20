@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

namespace RightComoduleHom

variable {R C M N P : Type*} [CommSemiring R]

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable [AddCommMonoid P] [Module R P]

variable {X : RightComodule R C M} {Y : RightComodule R C N} {Z : RightComodule R C P}

/-- The identity right-comodule morphism. -/
def id (X : RightComodule R C M) : RightComoduleHom X X where
  toLinearMap := LinearMap.id
  colinear := by simp [LinearMap.rTensor_id]

end RightComoduleHom
end Coalgebra
end
