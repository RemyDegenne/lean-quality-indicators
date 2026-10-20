@[expose] public section

noncomputable section

universe u

namespace SplitQuadric.Examples

open SplitQuadric

variable (A : Type u) [CommRing A]

theorem coordinate_eq_zero [Subsingleton A] (i : Fin 4) : coordinate A i = 0 :=
  Subsingleton.elim _ _

end SplitQuadric.Examples
end
end
