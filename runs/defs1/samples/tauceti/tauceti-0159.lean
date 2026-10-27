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

local notation "𝔽₂" => ZMod 2

local notation "H₂₆" => GeneralLinear.coordinateHopfAlgebra 𝔽₂ 26

local notation "J" => CommHopfAlgCat.commonKernelHopfIdeal generator

local notation "Q" => CommHopfAlgCat.quotient H₂₆ J

/-- Points of the scalar-extended carrier coordinate algebra are the named matrix-valued
prime-field carrier points over the extension ring. -/
noncomputable def baseChangePointsEquiv (k : Type v) [CommRing k] [Algebra 𝔽₂ k] :
    HopfAlgebra.points (R := k) (H := CommHopfAlgCat.baseChange (K := k) Q)
      (CommAlgCat.of k k) ≃* points k :=
  (AlgHom.baseChangePointsMulEquiv (k := 𝔽₂) (K := k) (A := Q) (R := k)).symm.trans
    (coordinatePointsEquiv k)

end PrimeField
end TauCeti.F4ShortRoot
end
