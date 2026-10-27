@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- Compatibility name for the integral singular homology functor. -/
noncomputable abbrev integerSingularHomologyFunctor (n : ℕ) :
    TopCat.{u} ⥤ ModuleCat.{u, 0} ℤ :=
  integralSingularHomologyFunctor n

end TopCat
end
end
