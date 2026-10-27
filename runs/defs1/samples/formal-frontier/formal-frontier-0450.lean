@[expose] public section

open CategoryTheory Set

universe u v

namespace ProfiniteAddGrp

/-- A profinite additive group is procyclic when it has a topological
generator. -/
def IsProcyclic (G : ProfiniteAddGrp.{u}) : Prop :=
  ∃ g : G, IsTopologicalGenerator G g

end ProfiniteAddGrp
end
