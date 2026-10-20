@[expose] public section

namespace SimpleGraph

open Walk

theorem cycleGraph_zero_eq_bot : cycleGraph 0 = ⊥ := Subsingleton.elim _ _

end SimpleGraph
end
