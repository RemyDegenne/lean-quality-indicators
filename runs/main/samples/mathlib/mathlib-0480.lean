@[expose] public section

open Function (Surjective)

open Polynomial

section MonoidAlgebra

variable {R : Type*} {M : Type*}

namespace MonoidAlgebra

open Algebra Submonoid Submodule

variable [Monoid M]

theorem finiteType_iff_group_fg {G : Type*} [Group G] [CommRing R] [Nontrivial R] :
    FiniteType R R[G] ↔ Group.FG G := by
  simpa [Group.fg_iff_monoid_fg] using finiteType_iff_fg

end MonoidAlgebra
end MonoidAlgebra
end
