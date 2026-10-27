namespace P2MW.S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair

set_option autoImplicit false

set_option linter.unusedSectionVars false

open PDivisibleGroup

open scoped TensorProduct

open Coalgebra WithConv

namespace PDivAlphaZero

variable {R : Type} [CommRing R] {p h : ℕ}

section Alpha

variable [Fact p.Prime]

variable {G G' : PDivisibleGroup R p h} (D : G.CartierDuality G')

variable {L : Type} [CommRing L] [Algebra R L]

noncomputable def pt (z : G.Points L) : G.Point L (lv z) :=
  Classical.choose (Classical.choose_spec (Points.exists_mkAdd G z))

end Alpha
end PDivAlphaZero
end P2MW.S_PDivisibleGroup_CartierDuality_exists_points_tateModule_pairing_eq_pair
