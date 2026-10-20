public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β}

namespace Walk

variable {x y z w : α}

theorem IsCycle.isTrail {p : G.Walk x x} (hp : p.IsCycle) : p.IsTrail := hp.2.1

end Walk
end Graph
end
