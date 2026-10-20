public section

open AlgebraicGeometry CategoryTheory

open scoped Matrix

namespace TauCeti.F4ShortRoot

open TauCeti.DynkinType

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance high] Algebra.toModule

universe u v w

local notation "CM" => CartanMatrix.F₄ᵀ

local notation "rootGen" => TauCeti.serreRootGenerator CM

local notation "cartanGen" => TauCeti.serreH ℚ CM

local notation "rootWeight" => DynkinType.F4.rootGeneratorWeight DynkinType.valid_F4

namespace PrimeField

/-- The map on the points of the carrier over `𝔽₂` induced by a homomorphism of `𝔽₂`-algebras. -/
noncomputable def pointsMap {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra (ZMod 2) A]
    [Algebra (ZMod 2) B] (f : A →ₐ[ZMod 2] B) : points A →* points B :=
  TauCeti.GeneralLinear.mapHopfIdealPointsSubgroupCongr 26 definingIdeal
    (points_eq_hopfIdealPointsSubgroup A) (points_eq_hopfIdealPointsSubgroup B) f

end PrimeField
end TauCeti.F4ShortRoot
end
