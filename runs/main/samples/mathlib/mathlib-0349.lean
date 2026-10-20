@[expose] public section

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V) {u v w : V}

namespace Walk

variable {G}

theorem edges_eq_map_darts (p : G.Walk u v) : p.edges = p.darts.map Dart.edge :=
  rfl

end Walk
end SimpleGraph
end
