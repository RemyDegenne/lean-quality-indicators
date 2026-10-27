@[expose] public section

universe u

open CategoryTheory

open scoped Simplicial

namespace SSet

variable (X : SSet.{u})

namespace S

variable {X}

/-- This is the non degenerate simplex of a simplicial set which
generates the same subcomplex as a given simplex. -/
noncomputable def toN (x : X.S) : X.N := x.existsUnique_n.exists.choose

end S
end SSet
end
