public section

set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Topology

universe u v

namespace CompletedGroupAlgebra

/-- The inverse-limit topology on a completed group algebra, induced by all
finite-quotient projections. -/
@[expose, instance_reducible]
def inverseLimitTopology (R : Type u) [CommRing R] [TopologicalSpace R]
    (G : ProfiniteGrp.{v}) : TopologicalSpace (CompletedGroupAlgebra R G) :=
  ⨅ U, .induced (proj R G U)
    (finiteGroupAlgebraTopology R (G ⧸ U.toSubgroup))

end CompletedGroupAlgebra
end
end
