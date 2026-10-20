@[expose] public section

open CategoryTheory Limits AlgebraicTopology

open scoped Simplicial

noncomputable section

namespace TopCat

universe u

open ContinuousMap

/-- In every positive degree, reduced and ordinary integer singular homology
are canonically identical. -/
noncomputable def reducedSingularHomologyIsoOfNeZero (X : TopCat.{u}) (n : ℕ)
    (hn : n ≠ 0) :
    reducedSingularHomology X n ≅ integralSingularHomology X n :=
  match n with
  | 0 => (hn rfl).elim
  | _ + 1 => Iso.refl _

end TopCat
end
end
