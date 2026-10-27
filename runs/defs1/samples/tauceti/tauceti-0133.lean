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

/-- The rank-four split weight torus in the carrier over `𝔽₂`. -/
noncomputable def weightTorus : SplitTorus.groupScheme (ZMod 2) (Fin 4) ⟶ groupScheme :=
  eqToHom (DiagonalizableGroup.groupScheme_def (ZMod 2) (SplitTorus.characterGroup (Fin 4))) ≫
    TauCeti.GeneralLinear.generatorToGeneratedGroupScheme 26 generator (.inr ())

end PrimeField
end TauCeti.F4ShortRoot
end
