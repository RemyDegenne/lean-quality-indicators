public section

open CategoryTheory WithConv

open scoped Matrix TensorProduct

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

universe u

noncomputable section

variable (k : Type u) [CommRing k] [Algebra (ZMod 2) k]

/-- The standard right comodule of the scalar-extended short-root carrier on `k²⁶`. -/
@[instance_reducible]
def standardComodule : Comodule k (coordinateHopfAlgebra k) (Fin 26 → k) :=
  GeneralLinear.corestrictStandardComodule k 26 (coordinateMap k).hom

end
end TauCeti.F4ShortRoot.PrimeField
end
