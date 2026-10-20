@[expose] public section

open scoped MonoidAlgebra

universe w w' u u' v v'

namespace Rep

open CategoryTheory Representation

variable {k : Type u} {G : Type v} [CommRing k]

variable (k G) [Monoid G] (A B : Rep.{w} k G)

variable {k G A B}

variable (k G)

/-- The functor sending `A, B` to `(A ⊗[k] B)_G`. This is naturally isomorphic to the functor
sending `A, B` to `A ⊗[k[G]] B`, where we give `A` the `k[G]ᵐᵒᵖ`-module structure defined by
`g • a := A.ρ g⁻¹ a`. -/
noncomputable abbrev coinvariantsTensor : Rep k G ⥤ Rep k G ⥤ ModuleCat k :=
  (Functor.postcompose₂.obj (coinvariantsFunctor k G)).obj (MonoidalCategory.curriedTensor _)

end Rep
end
