public section

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

/-- A chosen walk from the root of the connected component of a vertex to that vertex. -/
noncomputable def componentPath (v : V) : G.Walk (componentRoot G v) v :=
  (reachable_componentRoot G v).exists_path_of_dist.choose

end SimpleGraph
end
