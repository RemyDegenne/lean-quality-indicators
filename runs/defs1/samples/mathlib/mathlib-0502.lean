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

/-- The `k`-linear `G`-representation on `k[Gⁿ]`, induced by left multiplication. -/
abbrev diagonal (n : ℕ) : Rep k G :=
  ofMulAction k G (Fin n → G)

end setup
end ring
end
end Rep
end
