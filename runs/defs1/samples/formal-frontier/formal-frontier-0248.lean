@[expose] public section

open CategoryTheory

open Convexity TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace TopCat

/-- Singular simplices whose range is contained in one member of `U`. -/
def smallSingularSet {X : TopCat.{u}} {ι : Type*} (U : ι → Opens X) :
    (TopCat.toSSet.obj X).Subcomplex where
  obj n := {x | ∃ i, Set.range (X.toSSetObjEquiv n x) ⊆ U i}
  map {n m} f x hx := by
    rcases hx with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hi ⟨StdSimplex.map f.unop z, rfl⟩

end TopCat
end
end
