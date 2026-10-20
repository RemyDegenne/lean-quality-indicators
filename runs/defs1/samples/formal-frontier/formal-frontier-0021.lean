@[expose] public section

open CategoryTheory Set

universe u v

namespace ProfiniteGrp

/-- A profinite group is procyclic when it has a topological generator. -/
def IsProcyclic (G : ProfiniteGrp.{u}) : Prop :=
  ∃ g : G, IsTopologicalGenerator G g

end ProfiniteGrp
end
