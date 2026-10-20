@[expose] public section

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V) {u v w : V}

namespace Walk

variable {G}

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts {u v : V} : G.Walk u v → List G.Dart
  | nil => []
  | cons h p => p.darts

end Walk
end SimpleGraph
end
