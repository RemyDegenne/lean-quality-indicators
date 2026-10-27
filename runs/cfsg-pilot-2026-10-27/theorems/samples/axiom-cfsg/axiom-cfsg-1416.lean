public section

set_option linter.unusedSectionVars false

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77

open CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

section MinCex

variable {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCex.centralizer_ne_top (h6 : E18_6) (c : MinCex Ω K S R W H) {x : G}
    (hx : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≠ ⊤ :=
  CFSG.ClassicalInvolution.T7FU.Asc77.MinCex.centralizer_ne_top (h6.atG c) c.toU hx

end MinCex
end Asc77
end
end CFSG.ClassicalInvolution.Q3.Q3T8
end
