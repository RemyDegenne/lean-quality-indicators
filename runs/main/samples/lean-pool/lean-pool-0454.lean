@[expose] public section

namespace BollobasNikiforov

open Matrix Module.End Metric WithLp

open scoped InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {B : Matrix n n ℝ}

omit [DecidableEq n] in
lemma continuous_dotProduct_mulVec :
    Continuous fun x : n → ℝ => x ⬝ᵥ B *ᵥ x :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

end BollobasNikiforov
end
