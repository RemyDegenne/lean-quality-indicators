public section

universe u v

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type u) (L : Type v)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

theorem pbwFiltrationPrevious_def (k : ℕ) :
    pbwFiltrationPrevious R L k =
      TauCeti.Algebra.wordFiltrationPrevious
        (_root_.UniversalEnvelopingAlgebra.ι R).toLinearMap k := (rfl)

end TauCeti.UniversalEnvelopingAlgebra
end
