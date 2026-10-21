namespace OAI

namespace Superstring.BlockFactory

open BitCode Hierarchical WalkCode LayerArray BlockClose

variable {α : Type} [Coded α] [Inhabited α] [DecidableEq α]

@[fun_prop] theorem poly_collective : Poly (fun q : CollectiveInput α =>
    collective q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold collective
  exact poly_pack.comp
    (f := fun q : CollectiveInput α => (q.1,(q.2.1.1,q.2.2.1,q.2.2.2.1),
      (band q.1.1 q.2.1.1 q.2.1.2.1 q.2.1.2.2 (q.2.1.1.length-1) q.2.2.2.2,
       [LayerArray.collective q.1.1 q.2.1.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1,
        shortSweep q.1.1 q.2.1.1 q.2.1.2.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2]))) (by fun_prop)

end Superstring.BlockFactory
end OAI
