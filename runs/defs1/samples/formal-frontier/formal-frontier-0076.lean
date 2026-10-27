@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- The degree-zero homology class represented by a point. -/
noncomputable def singularHomologyZeroPoint (X : TopCat.{u}) (x : X) :
    singularHomologyIntegerCoefficients ⟶ (integralSingularHomologyFunctor 0).obj X :=
  show singularHomologyIntegerCoefficients ⟶
      (toSSet.obj X).homology singularHomologyIntegerCoefficients 0 from
    SSet.homologyZeroPoint (toSSet.obj X) singularHomologyIntegerCoefficients
      (toSSetObj₀Equiv.symm x)

end TopCat
end
end
