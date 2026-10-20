set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[simp] theorem quotientTransitionHom_mk (N M : OpenNormalSubgroup G) (hNM : N ≤ M)
    (g : G) :
    quotientTransitionHom N M hNM (QuotientGroup.mk' N.toSubgroup g) =
      QuotientGroup.mk' M.toSubgroup g := rfl

end ContinuousCohomology
end
