public section

universe u v w x

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R

variable {ιIndex : Type w}

/-- The PBW monomial attached to a word of indices in a family `e : ιIndex → L`. No ordering or
linear-independence hypothesis on the family is needed. -/
def pbwMonomial (e : ιIndex → L) (word : List ιIndex) :
    _root_.UniversalEnvelopingAlgebra R L :=
  ((word.map e).map ⇑ι).prod

end TauCeti.UniversalEnvelopingAlgebra
end
