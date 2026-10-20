@[expose] public section

open Bornology Filter Metric Set Topology

open scoped NNReal

variable {α β : Type*} [PseudoMetricSpace α]

namespace MulOpposite

@[to_additive (attr := simp)]
lemma nndist_unop (x y : αᵐᵒᵖ) : nndist (unop x) (unop y) = nndist x y := rfl

end MulOpposite
end
