@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

@[reassoc (attr := simp)]
theorem singularHomologyZeroPoint_augmentation (X : TopCat.{u}) (x : X) :
    singularHomologyZeroPoint X x ≫
        X.singularHomology₀ε singularHomologyIntegerCoefficients =
      𝟙 singularHomologyIntegerCoefficients := by
  change singularHomologyZeroPoint X x ≫
      (toSSet.obj X).homology₀ε singularHomologyIntegerCoefficients = _
  exact SSet.homologyZeroPoint_augmentation
    (toSSet.obj X) singularHomologyIntegerCoefficients
    (toSSetObj₀Equiv.symm x)

end TopCat
end
end
