@[expose] public section

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- The type of nondegenerate simplices which do not belong to
a given subcomplex of a simplicial set. -/
structure N extends X.N where mk' ::
  notMem : simplex ∉ A.obj _

end SSet.Subcomplex
end
