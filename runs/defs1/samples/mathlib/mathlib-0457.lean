@[expose] public section

universe v u

open CategoryTheory Limits Functor ConcreteCategory

open scoped Simplicial

namespace SSet

open SimplexCategory

section adjunctions

/-- The adjunction between n-truncation and the n-coskeleton. -/
noncomputable def coskAdj (n : ℕ) : truncation.{u} n ⊣ Truncated.cosk n :=
  SimplicialObject.coskAdj n

end adjunctions
end SSet
end
