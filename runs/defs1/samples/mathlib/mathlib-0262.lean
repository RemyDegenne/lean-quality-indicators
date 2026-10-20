@[expose] public section

universe w w' u u' v v'

open CategoryTheory

open scoped MonoidAlgebra

namespace Rep

noncomputable section

attribute [instance] hV1

attribute [instance 1100] hV2

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

noncomputable section Linearization

variable (k G)

noncomputable section Finsupp

open Finsupp

variable (α : Type u') (A : Rep k G)

variable {k G} in
/-- The representation on `α →₀ A` defined pointwise by a representation on `A`. -/
abbrev finsupp : Rep k G :=
  Rep.of (Representation.finsupp A.ρ α)

end Finsupp
end Linearization
end
end Rep
end
