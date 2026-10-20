set_option warningAsError true

set_option backward.isDefEq.respectTransparency.types false

@[expose] public section

universe u v w

open CategoryTheory TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable (X : TopRep.{max v w} k G)

@[simp] theorem quotientTransitionIncl_val {N M : OpenNormalSubgroup G} (hNM : N ≤ M)
    (x : TopRep.quotientInvariants M.toSubgroup X) :
    ((quotientTransitionIncl X hNM).hom x).1 = x.1 := rfl

end ContinuousCohomology
end
