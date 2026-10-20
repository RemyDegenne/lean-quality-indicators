@[expose] public section

open Matrix Set Filter

open scoped Topology

namespace BollobasNikiforov

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
lemma continuous_vecMulVec_self :
    Continuous fun p : n → ℝ ↦ vecMulVec p p :=
  continuous_id.matrix_vecMulVec continuous_id

end BollobasNikiforov
end
