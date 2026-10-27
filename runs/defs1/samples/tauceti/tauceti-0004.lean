public section

open CategoryTheory

namespace TauCeti.GeneralLinear

universe u w

noncomputable section

variable {R : Type u} [CommRing R] (n : ℕ)

variable (I : HopfIdeal R (coordinateHopfAlgebra R n))

/-- The group-valued functor sending a commutative `R`-algebra to the matrix point group cut out by
a fixed Hopf ideal in the coordinate ring of `GLₙ`. Its values are universe-lifted so that its
codomain agrees with the generic Hopf-algebra points functor. -/
def hopfIdealPointsSubgroupFunctor :
    CommAlgCat.{w} R ⥤ GrpCat.{max u w} :=
  hopfIdealPointsSubgroupFunctorUnlifted n I ⋙ GrpCat.uliftFunctor.{u, w}

end
end TauCeti.GeneralLinear
end
