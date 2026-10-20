@[expose] public section

universe w w' u u' v v'

open CategoryTheory

open scoped MonoidAlgebra

namespace Rep

noncomputable section

attribute [instance] hV1

attribute [instance 1100] hV2

section ring

variable {k : Type u} {G : Type v} [Ring k] [Monoid G]

section setup

variable (k G)

section

variable (M G : Type*) [Monoid M] [CommGroup G] [MulDistribMulAction M G]

/-- Turns a `CommGroup` `G` with a `MulDistribMulAction` of a monoid `M` into a
`ℤ`-linear `M`-representation on `Additive G`. -/
def ofMulDistribMulAction : Rep ℤ M := Rep.of (Representation.ofMulDistribMulAction M G)

end
end setup
end ring
end
end Rep
end
