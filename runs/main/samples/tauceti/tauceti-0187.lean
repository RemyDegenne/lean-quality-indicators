public section

open AlgebraicGeometry CategoryTheory

open scoped Matrix

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

local notation "CM" => CartanMatrix.F₄ᵀ

local notation "rootGen" => TauCeti.serreRootGenerator CM

local notation "cartanGen" => TauCeti.serreH ℚ CM

local notation "rootWeight" => DynkinType.F4.rootGeneratorWeight DynkinType.valid_F4

namespace PrimeField

universe u

@[simp]
theorem finiteTypeCoordinateHopfAlgebra_baseChange_obj
    (k : Type u) [CommRing k] [Algebra (ZMod 2) k] :
    (FiniteTypeCommHopfAlgCat.baseChange (K := k) finiteTypeCoordinateHopfAlgebra).obj =
      coordinateHopfAlgebra k :=
  rfl

end PrimeField
end TauCeti.F4ShortRoot
end
