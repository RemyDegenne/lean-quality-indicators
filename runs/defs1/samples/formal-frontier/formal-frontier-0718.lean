@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- Nonnegative reduced singular homology.  Degree zero is the augmentation
kernel, and positive degrees are ordinary integer singular homology. -/
noncomputable def reducedSingularHomologyFunctor (n : ℕ) :
    TopCat.{u} ⥤ ModuleCat.{u, 0} ℤ :=
  match n with
  | 0 => reducedSingularHomologyZeroFunctor
  | n + 1 => integralSingularHomologyFunctor (n + 1)

end TopCat
end
end
